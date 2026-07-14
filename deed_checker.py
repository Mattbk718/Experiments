#!/usr/bin/env python3
"""
Deed Checker — scans NYSCEF Affidavits of Service / Due Diligence for every
FC Mailers case that has a docket ID, extracts served-party names/addresses
via the Claude API, filters out non-natural persons (banks, LLCs, municipalities,
etc.), saves PDFs locally, and adds any new natural-person mailing targets to the
FC Mailers sheet. Emails a full report for manual review.
"""

import json
import os
import re
import subprocess
import sys
import time
import random
import shutil
import difflib
import smtplib
import tempfile
import urllib.request as _urllib_req
from datetime import date
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from pathlib import Path
from urllib.parse import quote, urljoin

import anthropic
import smartsheet
from playwright.sync_api import sync_playwright
import pdfplumber
try:
    import PyPDF2
except ImportError:
    PyPDF2 = None

from nyscef_tracker import (
    NYSCEF_HOME, DOC_LIST_BASE, cell_value, str_val, _find_max_page,
)

CHROME_BIN         = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
CHROME_PROFILE_DIR = Path.home() / "Library/Application Support/Google/Chrome"
CDP_URL            = "http://localhost:9222"


def _cdp_ready():
    try:
        _urllib_req.urlopen(f"{CDP_URL}/json/version", timeout=1)
        return True
    except Exception:
        return False


def launch_deed_checker_context(p):
    """Launch Chrome with remote debugging, patching the profile so Chrome
    downloads PDFs instead of opening them in its built-in viewer.

    Chrome's built-in PDF viewer makes it impossible to capture raw PDF bytes
    via Playwright — this preference patch (`plugins.always_open_pdf_externally`)
    forces Chrome to treat PDF responses as file downloads, which Playwright
    can intercept cleanly with page.expect_download().
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

        # Patch: make Chrome download PDFs rather than view them inline
        prefs_path = dst_profile / "Preferences"
        if prefs_path.exists():
            try:
                prefs = json.loads(prefs_path.read_text(encoding="utf-8"))
                prefs.setdefault("plugins", {})["always_open_pdf_externally"] = True
                prefs_path.write_text(json.dumps(prefs), encoding="utf-8")
                print("  Patched: plugins.always_open_pdf_externally = true")
            except Exception as e:
                print(f"  Warning: could not patch Chrome prefs: {e}")

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

SHEET_ID      = 6833160014063492  # FC Mailers
EMAIL_TO      = "matt.zeltser@gmail.com"
GMAIL_USER    = os.environ.get("GMAIL_USER", "matt.zeltser@gmail.com")
GMAIL_PASS    = os.environ.get("GMAIL_APP_PASSWORD", "")
AFFIDAVIT_DIR = Path.home() / "Dropbox" / "NYSCEF Affidavits"

CID = {
    "filing":     4007717321871236,
    "checked":    2822399730077572,
    "index":      5054516434888580,
    "title":      3668831891154820,
    "first":      5335991411599236,
    "last":       5920631704840068,
    "subject":    3084191597913988,
    "address":    7587791225284484,
    "city":       1958291691071364,
    "state":      6461891318441860,
    "zip":        4210091504756612,
    "plaintiff":  8713691132127108,
    "county":     550916807518084,
    "date_sent":  2802716621203332,
    "num_sent":   2906744436248452,
    "bounced":    7306316248573828,
    "door_knock": 1676816714360708,
    "nyscef":     5668718826442628,
}

AFFIDAVIT_DOC_TYPES = ("affidavit of service", "affidavit of due diligence")

CLAUDE_PARSE_PROMPT = """\
You are a legal document analyst. Read the affidavit text below and identify every \
NATURAL PERSON (a real human being) who was served or attempted to be served, along \
with their address.

Rules:
- Include only real individuals — NOT corporations, LLCs, partnerships, banks, \
  trusts, government agencies, municipalities, or other legal entities.
- Do NOT include the process server, notary, or attorney.
- For each person, extract: title (Mr./Mrs./Ms. if present, else empty string), \
  first name, last name, street address, city, state (2-letter abbreviation), \
  and 5-digit zip code.
- If any address field is missing or unclear, leave it as an empty string.
- Return ONLY valid JSON — an array of objects with keys: \
  title, first, last, street, city, state, zip.

Affidavit text:
\"\"\"
{text}
\"\"\"
"""


# ── Smartsheet helpers ───────────────────────────────────────────────────────

def norm(s):
    return re.sub(r"[^A-Z0-9]", "", (s or "").upper())


def load_existing_by_index(sheet):
    """index -> {docket, plaintiff, county, keys(set of normalized name+addr), rows}"""
    by_index = {}
    for row in sheet.rows:
        idx = str_val(cell_value(row, CID["index"]))
        if not idx:
            continue
        entry = by_index.setdefault(
            idx, {"docket": "", "plaintiff": "", "county": "", "keys": set(), "rows": []}
        )
        entry["rows"].append(row)

        docket = str_val(cell_value(row, CID["nyscef"]))
        if docket and not entry["docket"]:
            entry["docket"] = docket
        plaintiff = str_val(cell_value(row, CID["plaintiff"]))
        if plaintiff and not entry["plaintiff"]:
            entry["plaintiff"] = plaintiff
        county = str_val(cell_value(row, CID["county"]))
        if county and not entry["county"]:
            entry["county"] = county

        first = str_val(cell_value(row, CID["first"]))
        last  = str_val(cell_value(row, CID["last"]))
        addr  = str_val(cell_value(row, CID["address"])) or str_val(cell_value(row, CID["subject"]))
        zipc  = str_val(cell_value(row, CID["zip"]))
        key   = norm(f"{first} {last} {addr} {zipc}")
        if key:
            entry["keys"].add(key)
    return by_index


def is_duplicate_key(key, keyset, threshold=0.85):
    if key in keyset:
        return True
    return any(difflib.SequenceMatcher(None, key, k).ratio() >= threshold for k in keyset)


def build_row(ss, idx, entry, p):
    full_address = f"{p['street']}, {p['city']}, {p['state']} {p['zip']}".strip(", ")
    cells = [
        ss.models.Cell({"column_id": CID["index"],     "value": idx}),
        ss.models.Cell({"column_id": CID["first"],     "value": p["first"]}),
        ss.models.Cell({"column_id": CID["last"],      "value": p["last"]}),
        ss.models.Cell({"column_id": CID["subject"],   "value": full_address}),
        ss.models.Cell({"column_id": CID["address"],   "value": p["street"]}),
        ss.models.Cell({"column_id": CID["city"],      "value": p["city"]}),
        ss.models.Cell({"column_id": CID["state"],     "value": p["state"]}),
        ss.models.Cell({"column_id": CID["zip"],       "value": p["zip"]}),
        ss.models.Cell({"column_id": CID["plaintiff"], "value": entry["plaintiff"]}),
        ss.models.Cell({"column_id": CID["county"],    "value": entry["county"]}),
        ss.models.Cell({"column_id": CID["nyscef"],    "value": entry["docket"]}),
        ss.models.Cell({"column_id": CID["bounced"],   "value": False}),
        ss.models.Cell({"column_id": CID["door_knock"],"value": False}),
    ]
    if p.get("title"):
        cells.append(ss.models.Cell({"column_id": CID["title"], "value": p["title"]}))
    return ss.models.Row({"cells": cells})


# ── Claude API parsing ────────────────────────────────────────────────────────

def parse_affidavit_with_claude(client, text):
    """
    Use the Claude API to extract natural persons and their addresses from
    affidavit text. Returns a list of dicts with keys:
    title, first, last, street, city, state, zip.
    Falls back to an empty list on any error.
    """
    if not text or not text.strip():
        return []

    # Truncate to avoid token limits while keeping the most relevant content
    truncated = text[:12000]

    try:
        response = client.messages.create(
            model="claude-opus-4-7",
            max_tokens=1024,
            messages=[{
                "role": "user",
                "content": CLAUDE_PARSE_PROMPT.format(text=truncated),
            }],
        )
        raw = response.content[0].text.strip()
        # Strip markdown code fences if present
        raw = re.sub(r"^```(?:json)?\s*", "", raw)
        raw = re.sub(r"\s*```$", "", raw)
        parsed = json.loads(raw)
        if not isinstance(parsed, list):
            return []
        results = []
        for item in parsed:
            if not isinstance(item, dict):
                continue
            first = str(item.get("first", "")).strip()
            last  = str(item.get("last", "")).strip()
            if not first or not last:
                continue
            results.append({
                "title":  str(item.get("title", "")).strip(),
                "first":  first,
                "last":   last,
                "street": str(item.get("street", "")).strip(),
                "city":   str(item.get("city", "")).strip(),
                "state":  str(item.get("state", "")).strip(),
                "zip":    str(item.get("zip", "")).strip(),
            })
        return results
    except Exception as e:
        print(f"    Claude parse failed: {e}")
        return []


# ── PDF helpers ───────────────────────────────────────────────────────────────

def _safe_filename(label, max_len=80):
    """Sanitize a document label for use as a filename."""
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", label)
    return name[:max_len].rstrip(". ")


def save_and_extract_pdf(pdf_bytes, case_dir, filename):
    """Save PDF bytes to case_dir/filename.pdf and return extracted text."""
    case_dir.mkdir(parents=True, exist_ok=True)
    pdf_path = case_dir / (filename + ".pdf")

    # Don't re-download if we already have this file
    if not pdf_path.exists():
        pdf_path.write_bytes(pdf_bytes)
        print(f"    Saved: {pdf_path}")
    else:
        print(f"    Already saved: {pdf_path}")

    text = ""
    try:
        with pdfplumber.open(pdf_path) as pdf:
            text = "\n".join(page.extract_text() or "" for page in pdf.pages)
    except Exception as e:
        print(f"    pdfplumber failed ({e}); trying PyPDF2…")
        if PyPDF2:
            try:
                reader = PyPDF2.PdfReader(str(pdf_path))
                text = "\n".join((p.extract_text() or "") for p in reader.pages)
            except Exception as e2:
                print(f"    PyPDF2 also failed ({e2})")
    return text


# ── NYSCEF document list scraping ────────────────────────────────────────────

def _click_for_url(context, page, link):
    """Click a document link and return the resolved URL (handles new tab or same-page nav)."""
    try:
        with context.expect_page(timeout=8_000) as pi:
            link.click()
        doc_page = pi.value
        doc_page.wait_for_load_state("domcontentloaded", timeout=15_000)
        url = doc_page.url
        doc_page.close()
        return url
    except Exception:
        try:
            link.click()
            page.wait_for_load_state("domcontentloaded", timeout=15_000)
            return page.url
        except Exception:
            return None


def collect_affidavit_docs(page, context, docket_id):
    """Return list of {"label": str, "url": str} for affidavit-type documents."""
    encoded_id = quote(docket_id, safe="")
    docs, seen = [], set()

    def scan_current_page():
        for row in page.query_selector_all("table.NewSearchResults tr"):
            text = row.inner_text() or ""
            text_lower = text.lower()
            if not any(dtype in text_lower for dtype in AFFIDAVIT_DOC_TYPES):
                continue
            link = row.query_selector("a")
            if not link:
                continue
            label = " ".join(text.split())[:150]
            href = link.get_attribute("href") or ""
            if href and not href.lower().startswith("javascript"):
                doc_url = urljoin(page.url, href)
            else:
                doc_url = _click_for_url(context, page, link)
            if doc_url and doc_url not in seen:
                seen.add(doc_url)
                docs.append({"label": label, "url": doc_url})

    page.goto(f"{DOC_LIST_BASE}?docketId={encoded_id}&display=all",
              wait_until="domcontentloaded", timeout=30_000)
    try:
        page.wait_for_selector("table.NewSearchResults", timeout=8_000)
    except Exception:
        return docs
    scan_current_page()

    max_pg = _find_max_page(page)
    for pg in range(2, max_pg + 1):
        try:
            page.goto(f"{DOC_LIST_BASE}?docketId={encoded_id}&PageNum={pg}&narrow=",
                      wait_until="domcontentloaded", timeout=20_000)
            page.wait_for_selector("table.NewSearchResults", timeout=8_000)
        except Exception:
            break
        scan_current_page()

    return docs


def download_pdf_bytes(context, url):
    """Download a NYSCEF document PDF via Chrome's download mechanism.

    With `plugins.always_open_pdf_externally = true` set in Chrome's profile,
    Chrome treats PDF responses as file downloads rather than opening them in
    the built-in viewer.  Playwright's expect_download() captures the file
    before it reaches the filesystem, giving us the raw PDF bytes.
    """
    new_page = context.new_page()
    try:
        with new_page.expect_download(timeout=30_000) as dl_info:
            try:
                new_page.goto(url, wait_until="commit", timeout=30_000)
            except Exception as nav_err:
                # Playwright raises "Download is starting" when a navigation
                # triggers a download — this is expected; dl_info captures it.
                if "download" not in str(nav_err).lower():
                    raise
        download = dl_info.value
        data = Path(download.path()).read_bytes()
        return data if data[:4] == b"%PDF" else None
    except Exception as e:
        print(f"    Download failed for {url}: {e}")
        return None
    finally:
        try:
            new_page.close()
        except Exception:
            pass


# ── email report ──────────────────────────────────────────────────────────────

def send_report_email(report_lines, cases_checked, added_count, errors):
    if not GMAIL_PASS:
        print("(Email skipped — GMAIL_APP_PASSWORD not set.)")
        return

    today_label = date.today().strftime("%B %d, %Y")
    subject = f"Deed Checker Report — {today_label} ({added_count} new mailer(s))"
    body = (
        f"Deed Checker run — {today_label}\n"
        f"Cases checked: {cases_checked}   New rows added: {added_count}   Errors: {errors}\n"
        + "=" * 70 + "\n"
        + "\n".join(report_lines)
        + "\n\n— Deed Checker (review all NEW entries above before mailing/door-knocking)"
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
        print(f"✉  Report emailed to {EMAIL_TO}")
    except Exception as e:
        print(f"  Email failed: {e}")


# ── main ─────────────────────────────────────────────────────────────────────

def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=0,
                        help="Process only first N cases (0 = all)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Parse and report only; do not write to Smartsheet")
    args = parser.parse_args()

    ss_token = os.environ.get("SMARTSHEET_API_TOKEN")
    if not ss_token:
        sys.exit("Error: SMARTSHEET_API_TOKEN environment variable not set.")

    anthropic_key = os.environ.get("ANTHROPIC_API_KEY")
    if not anthropic_key:
        sys.exit("Error: ANTHROPIC_API_KEY environment variable not set.")

    claude = anthropic.Anthropic(api_key=anthropic_key)

    ss = smartsheet.Smartsheet(ss_token)
    ss.errors_as_exceptions(True)

    print("Fetching FC Mailers sheet…")
    sheet = ss.Sheets.get_sheet(SHEET_ID)
    by_index = load_existing_by_index(sheet)
    cases = [(idx, e) for idx, e in by_index.items() if e["docket"]]
    print(f"{len(cases)} unique case(s) with a NYSCEF Docket ID.")
    if args.limit > 0:
        cases = cases[:args.limit]
        print(f"(Limited to first {args.limit} case(s) for testing.)")

    AFFIDAVIT_DIR.mkdir(parents=True, exist_ok=True)

    report_lines  = []
    new_rows      = []
    cases_checked = 0
    errors        = 0

    with sync_playwright() as pw:
        context, browser, chrome_proc, chrome_tmp = launch_deed_checker_context(pw)
        page = context.new_page()

        print("Warming up NYSCEF session…")
        try:
            page.goto(NYSCEF_HOME, timeout=20_000, wait_until="domcontentloaded")
        except Exception as e:
            print(f"  Warning: homepage warmup failed ({e}) — continuing anyway.")

        for idx, entry in cases:
            docket = entry["docket"]
            print(f"\n[{idx}] docket={docket[:16]}…")
            report_lines.append(
                f"\nCase {idx}  (Plaintiff: {entry['plaintiff'] or '?'}, "
                f"County: {entry['county'] or '?'})"
            )
            cases_checked += 1
            case_dir = AFFIDAVIT_DIR / idx

            try:
                docs = collect_affidavit_docs(page, context, docket)
            except Exception as e:
                print(f"  Error loading document list: {e}")
                report_lines.append(f"  ERROR loading document list: {e}")
                errors += 1
                time.sleep(random.uniform(5, 10))
                continue

            if not docs:
                report_lines.append(
                    "  No AFFIDAVIT OF SERVICE / DUE DILIGENCE documents found."
                )
                print("  No affidavit documents found.")
                time.sleep(random.uniform(5, 10))
                continue

            for doc_num, doc in enumerate(docs, 1):
                print(f"  [{doc_num}/{len(docs)}] {doc['label'][:80]}")
                pdf_bytes = download_pdf_bytes(context, doc["url"])
                if not pdf_bytes:
                    report_lines.append(f"  [{doc['label'][:60]}] could not download PDF.")
                    errors += 1
                    continue

                filename = _safe_filename(f"{doc_num:02d}_{doc['label']}")
                text = save_and_extract_pdf(pdf_bytes, case_dir, filename)

                if not text.strip():
                    report_lines.append(
                        f"  [{doc['label'][:60]}] no extractable text "
                        f"(possibly a scanned image)."
                    )
                    time.sleep(random.uniform(2, 4))
                    continue

                parsed = parse_affidavit_with_claude(claude, text)
                if not parsed:
                    report_lines.append(
                        f"  [{doc['label'][:60]}] Claude found no natural persons / "
                        f"addresses."
                    )
                    time.sleep(random.uniform(2, 4))
                    continue

                for p in parsed:
                    label = f"{p['title']} {p['first']} {p['last']}".strip()
                    full_address = (
                        f"{p['street']}, {p['city']}, {p['state']} {p['zip']}".strip(", ")
                    )
                    key = norm(f"{p['first']} {p['last']} {p['street']} {p['zip']}")
                    if is_duplicate_key(key, entry["keys"]):
                        report_lines.append(
                            f"  Already on file: {label} — {full_address}"
                        )
                        continue
                    entry["keys"].add(key)
                    report_lines.append(
                        f"  NEW: {label} — {full_address}  "
                        f"(source: {doc['label'][:60]})"
                    )
                    print(f"    * NEW: {label} — {full_address}")
                    if not args.dry_run:
                        new_rows.append(build_row(ss, idx, entry, p))

                time.sleep(random.uniform(2, 4))

            time.sleep(random.uniform(5, 10))

        browser.close()
        if chrome_proc:
            chrome_proc.terminate()
        if chrome_tmp:
            shutil.rmtree(chrome_tmp, ignore_errors=True)
            print(f"  Cleaned up temp Chrome profile: {chrome_tmp}")

    added_count = 0
    if new_rows:
        print(f"\nAdding {len(new_rows)} new row(s) to FC Mailers…")
        for i in range(0, len(new_rows), 500):
            batch = new_rows[i:i + 500]
            try:
                ss.Sheets.add_rows(SHEET_ID, batch)
                added_count += len(batch)
            except Exception as e:
                print(f"  Batch add failed ({e}); retrying one-by-one…")
                for r in batch:
                    try:
                        ss.Sheets.add_rows(SHEET_ID, [r])
                        added_count += 1
                    except Exception as re:
                        print(f"    Skipping row: {re}")
        print(f"  Added {added_count} row(s).")
    elif args.dry_run:
        print("\nDry run — no rows written to Smartsheet.")
    else:
        print("\nNo new mailing targets found.")

    print(f"\n{'='*70}")
    print(f"  Checked {cases_checked} case(s), added {added_count} row(s), {errors} error(s).")
    print(f"{'='*70}\n")

    send_report_email(report_lines, cases_checked, added_count, errors)


if __name__ == "__main__":
    main()
