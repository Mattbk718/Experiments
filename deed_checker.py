#!/usr/bin/env python3
"""
Deed Checker — scans NYSCEF Affidavits of Service for every FC Mailers case
that has a docket ID, extracts served-party names/addresses, filters out
non-natural persons (banks, LLCs, municipalities, etc.), and adds any new
natural-person mailing targets to the FC Mailers sheet. Emails a full report
of everything found for manual review.

Best-effort parsing: affidavit-of-service PDFs come from many different
process servers with wildly different formats, so name/address extraction is
heuristic. Every parsed entry (added, already-on-file, or filtered out) is
included in the report email so nothing is added to the sheet unreviewed.
"""

import os
import re
import sys
import time
import random
import shutil
import difflib
import smtplib
import tempfile
from datetime import date
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from pathlib import Path
from urllib.parse import quote, urljoin

import smartsheet
from playwright.sync_api import sync_playwright
import pdfplumber
try:
    import PyPDF2
except ImportError:
    PyPDF2 = None

from nyscef_tracker import (
    NYSCEF_HOME, DOC_LIST_BASE, launch_context, cell_value, str_val, _find_max_page,
)

SHEET_ID   = 6833160014063492  # FC Mailers
EMAIL_TO   = "matt.zeltser@gmail.com"
GMAIL_USER = os.environ.get("GMAIL_USER", "matt.zeltser@gmail.com")
GMAIL_PASS = os.environ.get("GMAIL_APP_PASSWORD", "")

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

STATE_ABBR = ("AL|AK|AZ|AR|CA|CO|CT|DE|FL|GA|HI|ID|IL|IN|IA|KS|KY|LA|ME|MD|MA|MI|MN|MS|MO|"
              "MT|NE|NV|NH|NJ|NM|NY|NC|ND|OH|OK|OR|PA|RI|SC|SD|TN|TX|UT|VT|VA|WA|WV|WI|WY|DC")

ADDRESS_RE = re.compile(
    rf"(\d{{1,6}}[^\n,]{{2,60}}?),\s*([A-Za-z .'\-]{{2,40}}),?\s*({STATE_ABBR})\s*(\d{{5}})(?:-\d{{4}})?"
)

NAME_RE = re.compile(r"\b([A-Z][A-Za-z'\-]+(?:\s+[A-Z]\.?)?(?:\s+[A-Z][A-Za-z'\-]+){1,2})\b")

NAME_STOPWORDS = {
    "SUMMONS", "COMPLAINT", "COURT", "STATE", "COUNTY", "NOTICE", "PENDENCY", "PLAINTIFF",
    "PLAINTIFFS", "DEFENDANT", "DEFENDANTS", "ACTION", "INDEX", "AFFIDAVIT", "SERVICE",
    "DEPONENT", "ATTORNEY", "ESQ", "SUPREME", "AGAINST", "ORDER", "JUDGMENT", "MOTION",
    "NEW", "YORK", "CITY", "OF", "THE", "AND", "FOR", "ON", "SERVED", "TRUE", "COPY",
    "WITHIN", "PERSON", "RESIDENCE", "PLACE", "ADDRESS", "DWELLING", "ABODE", "DOOR", "SAID",
}

NON_PERSON_KEYWORDS = [
    "LLC", "L.L.C", "INC", "CORP", "CO.", "COMPANY", "L.P.", " LP ", "LLP", "PLLC", "P.C.",
    "BANK", "N.A.", "NATIONAL ASSOCIATION", "TRUST", "TRUSTEE", "MORTGAGE", "LOAN",
    "SERVICING", "FINANCIAL", "CREDIT UNION", "ASSOCIATION", "HOLDINGS", "FUND", "PARTNERS",
    "GROUP", "SERVICES", "AUTHORITY", "MUNICIPAL", "CITY OF", "COUNTY OF", "STATE OF",
    "DEPARTMENT", "COMMISSIONER", "AGENCY", "IRS", "INTERNAL REVENUE", "UNITED STATES",
    "HOUSING", "DEVELOPMENT", "REVENUE", "OFFICE OF", "BOARD OF", "PROPERTY OWNERS",
    "CONDOMINIUM", "COOPERATIVE", " HOA ", "MANAGEMENT", "REALTY", "PROPERTIES",
    "PARTNERSHIP", "ESTATE OF", "JOHN DOE", "JANE DOE",
]


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
        last = str_val(cell_value(row, CID["last"]))
        addr = str_val(cell_value(row, CID["address"])) or str_val(cell_value(row, CID["subject"]))
        zipc = str_val(cell_value(row, CID["zip"]))
        key = norm(f"{first} {last} {addr} {zipc}")
        if key:
            entry["keys"].add(key)
    return by_index


def is_duplicate_key(key, keyset, threshold=0.85):
    if key in keyset:
        return True
    return any(difflib.SequenceMatcher(None, key, k).ratio() >= threshold for k in keyset)


def build_row(ss, idx, entry, p):
    cells = [
        ss.models.Cell({"column_id": CID["index"], "value": idx}),
        ss.models.Cell({"column_id": CID["first"], "value": p["first"]}),
        ss.models.Cell({"column_id": CID["last"], "value": p["last"]}),
        ss.models.Cell({"column_id": CID["subject"], "value": p["full_address"]}),
        ss.models.Cell({"column_id": CID["address"], "value": p["street"]}),
        ss.models.Cell({"column_id": CID["city"], "value": p["city"]}),
        ss.models.Cell({"column_id": CID["state"], "value": p["state"]}),
        ss.models.Cell({"column_id": CID["zip"], "value": p["zip"]}),
        ss.models.Cell({"column_id": CID["plaintiff"], "value": entry["plaintiff"]}),
        ss.models.Cell({"column_id": CID["county"], "value": entry["county"]}),
        ss.models.Cell({"column_id": CID["nyscef"], "value": entry["docket"]}),
        ss.models.Cell({"column_id": CID["bounced"], "value": False}),
        ss.models.Cell({"column_id": CID["door_knock"], "value": False}),
    ]
    if p["title"]:
        cells.append(ss.models.Cell({"column_id": CID["title"], "value": p["title"]}))
    return ss.models.Row({"cells": cells})


# ── name / address parsing ───────────────────────────────────────────────────

def is_natural_person(name):
    upper = f" {name.upper()} "
    if any(kw in upper for kw in NON_PERSON_KEYWORDS):
        return False
    words = name.split()
    if not (2 <= len(words) <= 4):
        return False
    if any(ch.isdigit() for ch in name):
        return False
    return True


def find_name_before(text, pos, window=250):
    snippet = text[max(0, pos - window):pos]
    candidates = NAME_RE.findall(snippet)
    for cand in reversed(candidates):
        words = [w.strip(".") for w in cand.split()]
        if len(words) < 2 or any(w.upper() in NAME_STOPWORDS for w in words):
            continue
        return cand.strip()
    return None


def guess_title(text, pos, name, window=250):
    start = max(0, pos - window)
    idx = text.rfind(name, start, pos)
    if idx == -1:
        return ""
    before = text[max(0, idx - 15):idx].upper()
    if "MRS." in before or "MRS " in before:
        return "Mrs."
    if "MR." in before or "MR " in before:
        return "Mr."
    return ""


def parse_affidavit(text):
    """Return list of dicts: title, first, last, street, city, state, zip, full_address, context."""
    results = []
    for m in ADDRESS_RE.finditer(text):
        street, city, st, zip5 = m.group(1).strip(), m.group(2).strip(), m.group(3), m.group(4)
        name = find_name_before(text, m.start())
        if not name or not is_natural_person(name):
            continue
        words = name.split()
        first, last = words[0].strip("."), words[-1].strip(".")
        title = guess_title(text, m.start(), name)
        context = " ".join(text[max(0, m.start() - 120):m.end() + 20].split())
        results.append({
            "title": title, "first": first, "last": last,
            "street": street, "city": city, "state": st, "zip": zip5,
            "full_address": f"{street}, {city}, {st} {zip5}",
            "context": context,
        })
    return results


# ── PDF extraction ────────────────────────────────────────────────────────────

def extract_pdf_text(pdf_bytes):
    fd, tmp_name = tempfile.mkstemp(suffix=".pdf")
    os.close(fd)
    tmp_path = Path(tmp_name)
    tmp_path.write_bytes(pdf_bytes)
    text = ""
    try:
        with pdfplumber.open(tmp_path) as pdf:
            text = "\n".join(page.extract_text() or "" for page in pdf.pages)
    except Exception as e:
        print(f"    pdfplumber failed ({e}); trying PyPDF2…")
        if PyPDF2:
            try:
                reader = PyPDF2.PdfReader(str(tmp_path))
                text = "\n".join((p.extract_text() or "") for p in reader.pages)
            except Exception as e2:
                print(f"    PyPDF2 also failed ({e2})")
    finally:
        tmp_path.unlink(missing_ok=True)
    return text


# ── NYSCEF document list scraping ────────────────────────────────────────────

def _click_for_url(context, page, link):
    """Click a document link and return the resolved document URL, whether it
    opens a new tab or navigates the current page."""
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
    """Return list of {"label": str, "url": str} for AFFIDAVIT OF SERVICE docs."""
    encoded_id = quote(docket_id, safe="")
    docs, seen = [], set()

    def scan_current_page():
        for row in page.query_selector_all("table.NewSearchResults tr"):
            text = row.inner_text() or ""
            if "affidavit of service" not in text.lower():
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
    try:
        resp = context.request.get(url, timeout=30_000)
        if resp.ok:
            body = resp.body()
            ctype = (resp.headers.get("content-type") or "").lower()
            if "pdf" in ctype or body[:4] == b"%PDF":
                return body
    except Exception as e:
        print(f"    Download failed for {url}: {e}")
    return None


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
    msg["From"] = GMAIL_USER
    msg["To"] = EMAIL_TO
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
    parser.add_argument("--limit", type=int, default=0, help="Process only first N cases (0 = all)")
    parser.add_argument("--dry-run", action="store_true", help="Parse and report only; do not write to Smartsheet")
    args = parser.parse_args()

    token = os.environ.get("SMARTSHEET_API_TOKEN")
    if not token:
        sys.exit("Error: SMARTSHEET_API_TOKEN environment variable not set.")

    ss = smartsheet.Smartsheet(token)
    ss.errors_as_exceptions(True)

    print("Fetching FC Mailers sheet…")
    sheet = ss.Sheets.get_sheet(SHEET_ID)
    by_index = load_existing_by_index(sheet)
    cases = [(idx, e) for idx, e in by_index.items() if e["docket"]]
    print(f"{len(cases)} unique case(s) with a NYSCEF Docket ID.")
    if args.limit > 0:
        cases = cases[:args.limit]
        print(f"(Limited to first {args.limit} case(s) for testing.)")

    report_lines = []
    new_rows = []
    cases_checked = 0
    errors = 0

    with sync_playwright() as pw:
        context, browser, chrome_proc, chrome_tmp = launch_context(pw)
        page = context.new_page()

        print("Warming up NYSCEF session…")
        try:
            page.goto(NYSCEF_HOME, timeout=20_000, wait_until="domcontentloaded")
        except Exception as e:
            print(f"  Warning: homepage warmup failed ({e}) — continuing anyway.")

        for idx, entry in cases:
            docket = entry["docket"]
            print(f"\n[{idx}] docket={docket[:16]}…")
            report_lines.append(f"\nCase {idx}  (Plaintiff: {entry['plaintiff'] or '?'}, County: {entry['county'] or '?'})")
            cases_checked += 1

            try:
                docs = collect_affidavit_docs(page, context, docket)
            except Exception as e:
                print(f"  Error loading document list: {e}")
                report_lines.append(f"  ERROR loading document list: {e}")
                errors += 1
                time.sleep(random.uniform(5, 10))
                continue

            if not docs:
                report_lines.append("  No AFFIDAVIT OF SERVICE documents found.")
                print("  No affidavit of service documents found.")
                time.sleep(random.uniform(5, 10))
                continue

            for doc in docs:
                print(f"  Found doc: {doc['label'][:80]}")
                pdf_bytes = download_pdf_bytes(context, doc["url"])
                if not pdf_bytes:
                    report_lines.append(f"  [{doc['label'][:60]}] could not download PDF.")
                    errors += 1
                    continue

                text = extract_pdf_text(pdf_bytes)
                if not text.strip():
                    report_lines.append(f"  [{doc['label'][:60]}] no extractable text (possibly a scanned image).")
                    time.sleep(random.uniform(2, 4))
                    continue

                parsed = parse_affidavit(text)
                if not parsed:
                    report_lines.append(f"  [{doc['label'][:60]}] no name/address pairs parsed.")
                    time.sleep(random.uniform(2, 4))
                    continue

                for p in parsed:
                    label = f"{p['title']} {p['first']} {p['last']}".strip()
                    key = norm(f"{p['first']} {p['last']} {p['street']} {p['zip']}")
                    if is_duplicate_key(key, entry["keys"]):
                        report_lines.append(f"  Already on file: {label} — {p['full_address']}")
                        continue
                    entry["keys"].add(key)
                    report_lines.append(
                        f"  NEW: {label} — {p['full_address']}  "
                        f"(source: {doc['label'][:60]}; context: \"{p['context'][:100]}\")"
                    )
                    print(f"    * NEW: {label} — {p['full_address']}")
                    if not args.dry_run:
                        new_rows.append(build_row(ss, idx, entry, p))

                time.sleep(random.uniform(2, 4))

            time.sleep(random.uniform(5, 10))

        browser.close()
        if chrome_proc:
            chrome_proc.terminate()
        if chrome_tmp:
            shutil.rmtree(chrome_tmp, ignore_errors=True)
            print(f"  Cleaned up temp profile: {chrome_tmp}")

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
