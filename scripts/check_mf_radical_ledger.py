#!/usr/bin/env python3
"""Gate the MF-radical paper ledger against the Lean development.

Three failure modes are checked, all of them silent otherwise:

1. the ledger names a declaration that does not exist (a rename, or a row that
   was aspirational when written);
2. the ledger names a declaration that the paper audit does not print, so
   nothing checks its axiom closure or its zero-input status;
3. the audit prints a closed endpoint that the ledger does not list, so the
   advertised surface is larger than the ledger admits.

This is a lexical check, like the other manuscript gates: it resolves names
against `lean_decls.build_index`, which tracks the namespace stack rather than
elaborating.  That is enough for the failure it guards against.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import build_index  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
LEDGER = REPO_ROOT / "metadata" / "MF_RADICAL_PAPER_LEDGER.md"
AUDIT = REPO_ROOT / "GroupApproximation" / "Endpoint" / "MFRadicalPaperAudit.lean"

ROW_RE = re.compile(r"^\|(?P<paper>[^|]+)\|\s*`(?P<decl>[^`]+)`\s*\|(?P<status>[^|]+)\|\s*$")
AUDIT_RE = re.compile(r"^#audit_closed_axioms\s+(?P<decl>\S+)\s*$")


def ledger_rows() -> list[tuple[str, str, str]]:
    if not LEDGER.exists():
        raise SystemExit(f"missing ledger: {LEDGER}")
    text = LEDGER.read_text(encoding="utf-8")
    try:
        body = text.split("<!-- LEDGER-ROWS -->", 1)[1].split("<!-- END-LEDGER-ROWS -->", 1)[0]
    except IndexError:
        raise SystemExit("ledger is missing its LEDGER-ROWS markers")
    rows = []
    for line in body.splitlines():
        m = ROW_RE.match(line.strip())
        if m:
            rows.append(
                (m.group("paper").strip(), m.group("decl").strip(), m.group("status").strip())
            )
    return rows


def audited_decls() -> list[str]:
    if not AUDIT.exists():
        raise SystemExit(f"missing audit file: {AUDIT}")
    out = []
    for line in AUDIT.read_text(encoding="utf-8").splitlines():
        m = AUDIT_RE.match(line.strip())
        if m:
            out.append(m.group("decl"))
    return out


def main() -> int:
    rows = ledger_rows()
    if not rows:
        print("mf-radical ledger: no rows found", file=sys.stderr)
        return 1

    index = build_index()
    audited = audited_decls()
    failures: list[str] = []

    for paper, decl, status in rows:
        if decl not in index:
            failures.append(f"row '{paper}': declaration '{decl}' does not exist")
        if status != "closed":
            failures.append(f"row '{paper}': status '{status}' is not 'closed'")
        if decl not in audited:
            failures.append(
                f"row '{paper}': '{decl}' is not printed by "
                f"{AUDIT.relative_to(REPO_ROOT)}, so nothing checks its axioms"
            )

    listed = {decl for _, decl, _ in rows}
    for decl in audited:
        if decl not in listed:
            failures.append(
                f"audit prints closed endpoint '{decl}' but the ledger does not list it"
            )

    if failures:
        print("mf-radical ledger: FAIL", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1

    print(f"mf-radical ledger: OK ({len(rows)} rows, all closed and audited)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
