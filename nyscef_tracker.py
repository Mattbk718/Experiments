#!/usr/bin/env python3
"""NYSCEF Tracker — scrapes filing dates across all tracked Smartsheet sheets weekly."""

import os
import re
import random
import shutil
import subprocess
import sys
import tempfile
import time
import smtplib
import urllib.request
from datetime import date, datetime
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from pathlib import Path
from urllib.parse import quote

import smartsheet
from playwright.sync_api import sync_playwright

NYSCEF_HOME        = "https://iapps.courts.state.ny.us/nyscef/HomePage"
DOC_LIST_BASE      = "https://iapps.courts.state.ny.us/nyscef/DocumentList"
EMAIL_TO           = "matt.zeltser@gmail.com"
GMAIL_USER         = os.environ.get("GMAIL_USER", "matt.zeltser@gmail.com")
GMAIL_PASS         = os.environ.get("GMAIL_APP_PASSWORD", "")
CHROME_BIN         = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
CHROME_PROFILE_DIR = Path.home() / "Library/Application Support/Google/Chrome"
CDP_URL            = "http://localhost:9222"
# Keys: id, name, col_index, col_county, col_nyscef, col_filing (None if absent),
#       col_checked (None if absent — rows without this are always considered stale)
SHEETS = [
    {
        "id":          6833160014063492,
        "name":        "FC Mailers",
        "col_index":   5054516434888580,
        "col_county":  550916807518084,
        "col_nyscef":  5668718826442628,
        "col_filing":  4007717321871236,
        "col_checked": 2822399730077572,
    },
    {
        "id":          4288369518399364,
        "name":        "New Sheet",
        "col_index":   5331451597066116,
        "col_county":  7301776434040708,
        "col_nyscef":  745841318203268,
        "col_filing":  None,
        "col_checked": 827851969695620,
    },
    {
        "id":          63527252348804,
        "name":        "Sales CRM",
        "col_index":   5625565667872644,
        "col_county":  547206399823748,
        "col_nyscef":  1929235913805700,
        "col_filing":  3520663894921092,
        "col_checked": 4402423130263428,
    },
    {
        "id":          3237454914998148,
        "name":        "Sales CRM 2",
        "col_index":   1615625186480004,
        "col_county":  3867425000165252,
        "col_nyscef":  1280323532132228,
        "col_filing":  2289348310765444,
        "col_checked": 3333547101556612,
    },
]

_DATE_RE = re.compile(r"\b(\d{1,2}/\d{1,2}/\d{4})\b")


# ── helpers ──────────────────────────────────────────────────────────────────

def cell_value(row, col_id):
    if col_id is None:
        return None
    for cell in row.cells:
        if cell.column_id == col_id:
            return cell.value
    return None


def str_val(v):
    return str(v).strip() if v is not None else ""


def parse_date(s):
    """Parse MM/DD/YYYY or YYYY-MM-DD into a date, or None."""
    if not s:
        return None
    for fmt in ("%m/%d/%Y", "%Y-%m-%d"):
        try:
            return datetime.strptime(s.strip(), fmt).date()
        except Exception:
            pass
    return None



# ── browser ───────────────────────────────────────────────────────────────────

def _cdp_ready():
    try:
        urllib.request.urlopen(f"{CDP_URL}/json/version", timeout=1)
        return True
    except Exception:
        return False


def launch_context(p):
    """
    Launch Chrome via subprocess with a copy of the real user profile and
    --remote-debugging-port=9222, then connect Playwright over CDP.
    Chrome rejects remote debugging on the default data directory, so we copy
    ~/Library/.../Chrome/Default into a temp dir and point --user-data-dir there.
    Returns (context, browser, proc, tmp_dir); proc and tmp_dir are None if
    Chrome was already running on port 9222.
    """
    proc = None
    tmp_dir = None
    if _cdp_ready():
        print("Connecting to already-running Chrome on port 9222…")
    else:
        src_profile = CHROME_PROFILE_DIR / "Default"
        tmp_dir = tempfile.mkdtemp(prefix="chrome_debug_")
        dst_profile = Path(tmp_dir) / "Default"
        print(f"Copying Chrome profile to {tmp_dir} …")
        shutil.copytree(src_profile, dst_profile, symlinks=True)
        print("  Profile copy done.")

        print("Launching Chrome with remote debugging on port 9222…")
        proc = subprocess.Popen([
            CHROME_BIN,
            "--remote-debugging-port=9222",
            f"--user-data-dir={tmp_dir}",
            "--no-first-run",
            "--no-default-browser-check",
        ])
        for i in range(120):
            if _cdp_ready():
                print(f"  Chrome ready after {(i + 1) * 0.5:.1f}s")
                break
            time.sleep(0.5)
        else:
            proc.terminate()
            shutil.rmtree(tmp_dir, ignore_errors=True)
            raise RuntimeError("Chrome did not open remote debugging port within 60 s.")

    browser = p.chromium.connect_over_cdp(CDP_URL)
    ctx = browser.contexts[0] if browser.contexts else browser.new_context()
    print(f"Browser: Google Chrome via CDP  (profile copy: {tmp_dir or 'pre-existing'})")
    return ctx, browser, proc, tmp_dir


# ── scraping ──────────────────────────────────────────────────────────────────

def _find_max_page(page):
    """Return the highest PageNum found in pagination links, or 1 if none."""
    try:
        links = page.query_selector_all("a[href*='PageNum=']")
        nums = []
        for link in links:
            href = link.get_attribute("href") or ""
            m = re.search(r'PageNum=(\d+)', href)
            if m:
                nums.append(int(m.group(1)))
        return max(nums) if nums else 1
    except Exception:
        return 1


def _last_row_date(page):
    """Return the most recent filing date found in table.NewSearchResults, or None.

    Scans every data row and returns the maximum date so that footer rows
    (which have <td> but no date) and uncertain sort orders don't matter.
    """
    any_date = re.compile(r'(\d{1,2}/\d{1,2}/\d{4})')
    try:
        rows = page.query_selector_all("table.NewSearchResults tr")
        data_rows = [r for r in rows if r.query_selector("td")]
        if not data_rows:
            print("    _last_row_date: no <td> rows found in table.NewSearchResults")
            return None
        best_dt, best_str = None, None
        for row in data_rows:
            text = row.inner_text() or ""
            for m in any_date.finditer(text):
                try:
                    dt = datetime.strptime(m.group(1), "%m/%d/%Y").date()
                    if best_dt is None or dt > best_dt:
                        best_dt, best_str = dt, m.group(1)
                except ValueError:
                    pass
        if best_str is None:
            print(f"    _last_row_date: no dates found in {len(data_rows)} rows")
        return best_str
    except Exception as exc:
        print(f"    _last_row_date exception: {exc}")
        return None


def scrape_latest_filing_date(page, docket_id):
    """
    Navigate to the NYSCEF document list and return the most recent Date Filed
    as MM/DD/YYYY, or None on failure.

    NYSCEF paginates oldest-first; the most recent filing is the last row of
    the last page.
    """
    encoded_id = quote(docket_id, safe="")
    url = f"{DOC_LIST_BASE}?docketId={encoded_id}&display=all"
    try:
        page.goto(url, timeout=30_000, wait_until="domcontentloaded")
        page.wait_for_selector("table.NewSearchResults", timeout=8_000)
        time.sleep(random.uniform(3, 5))
    except Exception as e:
        print(f"    Browser error for docket {docket_id}: {e}")
        return None

    max_pg = _find_max_page(page)
    if max_pg > 1:
        try:
            page.goto(
                f"{DOC_LIST_BASE}?docketId={encoded_id}&PageNum={max_pg}&narrow=",
                wait_until="domcontentloaded", timeout=30_000,
            )
            page.wait_for_selector("table.NewSearchResults", timeout=8_000)
        except Exception as e:
            print(f"    Could not load page {max_pg}: {e}")

    result = _last_row_date(page)
    if result is None:
        page.wait_for_timeout(2000)
        result = _last_row_date(page)

    if result is None:
        print(f"    No filing dates found on page for docket {docket_id}.")
    return result


def send_new_filing_email(new_filings):
    """
    Send a summary email for cases where a newer filing date was detected.
    Each entry: sheet, index, county, old_date, new_date.
    """
    if not GMAIL_PASS:
        print("  (Email skipped — GMAIL_APP_PASSWORD not set.)")
        return

    today_label = date.today().strftime("%B %d, %Y")
    subject = f"NYSCEF New Filings Detected — {today_label}"

    rows = "\n".join(
        f"  • [{f['sheet']}]  {f['index']:<22}  {f['county']:<14}  "
        f"{f['old_date'] or '(none)':<12}  →  {f['new_date']}"
        for f in new_filings
    )
    body = (
        f"New NYSCEF filings detected on {today_label}:\n\n"
        f"  {'Sheet':<14}  {'Index #':<22}  {'County':<14}  "
        f"{'Old Date':<12}     {'New Date'}\n"
        f"  {'-'*14}  {'-'*22}  {'-'*14}  {'-'*12}     {'-'*12}\n"
        f"{rows}\n\n"
        f"— NYSCEF Tracker"
    )

    msg = MIMEMultipart()
    msg["From"]    = GMAIL_USER
    msg["To"]      = EMAIL_TO
    msg["Subject"] = subject
    msg.attach(MIMEText(body, "plain"))

    try:
        with smtplib.SMTP("smtp.gmail.com", 587) as server:
            server.starttls()
            server.login(GMAIL_USER, GMAIL_PASS)
            server.sendmail(GMAIL_USER, EMAIL_TO, msg.as_string())
        print(f"  ✉  Email sent to {EMAIL_TO} ({len(new_filings)} new filing(s)).")
    except Exception as e:
        print(f"  Email failed: {e}")


# ── main ─────────────────────────────────────────────────────────────────────

def main():
    import argparse
    parser = argparse.ArgumentParser()
    args = parser.parse_args()

    token = os.environ.get("SMARTSHEET_API_TOKEN")
    if not token:
        sys.exit("Error: SMARTSHEET_API_TOKEN environment variable not set.")

    ss = smartsheet.Smartsheet(token)
    ss.errors_as_exceptions(True)

    today_str     = date.today().strftime("%Y-%m-%d")
    all_new       = []
    total_checked = 0
    total_updated = 0

    print(f"\n{'═'*70}")
    print(f"  NYSCEF TRACKER — {date.today().strftime('%A, %B %d, %Y')}")
    print(f"{'═'*70}\n")

    with sync_playwright() as pw:
        context, browser, chrome_proc, chrome_tmp = launch_context(pw)
        page = context.new_page()

        # Warm up session with homepage visit so the site sets any required cookies
        print("Warming up NYSCEF session…")
        try:
            page.goto(NYSCEF_HOME, timeout=20_000, wait_until="domcontentloaded")
        except Exception as e:
            print(f"  Warning: homepage warmup failed ({e}) — continuing anyway.")

        for cfg in SHEETS:
            sheet_id   = cfg["id"]
            sheet_name = cfg["name"]

            print(f"\nFetching '{sheet_name}' (id {sheet_id})…")
            try:
                sheet = ss.Sheets.get_sheet(sheet_id)
            except Exception as e:
                print(f"  Could not load sheet: {e}")
                continue

            row_updates = []

            # Group stale rows by docket ID so each unique docket is scraped once.
            by_docket = {}  # docket_id -> list of row objects
            for row in sheet.rows:
                nyscef_id = str_val(cell_value(row, cfg["col_nyscef"]))
                if not nyscef_id:
                    continue
                # Skip cells that contain a plain number instead of an encoded docket string
                try:
                    float(nyscef_id)
                    print(f"  Skipping row with numeric docket value: {nyscef_id!r}")
                    continue
                except ValueError:
                    pass
                by_docket.setdefault(nyscef_id, []).append(row)

            for nyscef_id, rows in by_docket.items():
                first_row = rows[0]
                idx       = str_val(cell_value(first_row, cfg["col_index"]))
                suffix    = f"  ({len(rows)} rows)" if len(rows) > 1 else ""
                print(f"  Checking {idx or '(no index)'}  docket={nyscef_id}{suffix}")

                total_checked += 1
                new_date_str = scrape_latest_filing_date(page, nyscef_id)
                delay = random.uniform(5, 10)
                print(f"    Waiting {delay:.1f}s before next lookup…")
                time.sleep(delay)

                for row in rows:
                    row_idx    = str_val(cell_value(row, cfg["col_index"]))
                    row_county = str_val(cell_value(row, cfg["col_county"]))
                    new_cells  = []

                    if new_date_str and cfg["col_filing"]:
                        old_filing_str = str_val(cell_value(row, cfg["col_filing"]))
                        old_dt = parse_date(old_filing_str)
                        new_dt = parse_date(new_date_str)
                        if new_dt and (old_dt is None or new_dt > old_dt):
                            print(f"    ★ New filing: {old_filing_str or '(none)'}  →  {new_date_str}")
                            all_new.append({
                                "sheet":    sheet_name,
                                "index":    row_idx,
                                "county":   row_county,
                                "old_date": old_filing_str,
                                "new_date": new_date_str,
                            })
                        iso_date = new_dt.strftime("%Y-%m-%d") if new_dt else new_date_str
                        filing_cell = ss.models.Cell()
                        filing_cell.column_id = cfg["col_filing"]
                        filing_cell.value = iso_date
                        new_cells.append(filing_cell)

                    # Always stamp Last Checked Court (even on scrape failure, to avoid hammering)
                    if cfg["col_checked"]:
                        checked_cell = ss.models.Cell()
                        checked_cell.column_id = cfg["col_checked"]
                        checked_cell.value = today_str
                        new_cells.append(checked_cell)

                    if new_cells:
                        new_row = ss.models.Row()
                        new_row.id = row.id
                        new_row.cells = new_cells
                        row_updates.append(new_row)

            for i in range(0, len(row_updates), 500):
                batch = row_updates[i : i + 500]
                try:
                    ss.Sheets.update_rows(sheet_id, batch)
                    total_updated += len(batch)
                    print(f"  ✓ Saved {len(batch)} row update(s) in '{sheet_name}'")
                except Exception as e:
                    print(f"  Batch save failed ({e}); retrying one-by-one to skip bad rows…")
                    for r in batch:
                        try:
                            ss.Sheets.update_rows(sheet_id, [r])
                            total_updated += 1
                        except Exception as re:
                            print(f"    Skipping row {r.id}: {re}")

            if not row_updates:
                print(f"  — No rows needed updating in '{sheet_name}'")

        browser.close()
        if chrome_proc:
            chrome_proc.terminate()
        if chrome_tmp:
            shutil.rmtree(chrome_tmp, ignore_errors=True)
            print(f"  Cleaned up temp profile: {chrome_tmp}")

    print(f"\n{'═'*70}")
    print(f"  Checked {total_checked} case(s), updated {total_updated} row(s).")
    print(f"{'═'*70}\n")

    if all_new:
        print(f"{len(all_new)} new filing(s) detected — sending email…")
        send_new_filing_email(all_new)
    else:
        print("No new filings detected — no email sent.")


if __name__ == "__main__":
    main()
