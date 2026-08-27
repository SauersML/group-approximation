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

from lean_decls import _strip_block_comments, build_index  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
LEDGER = REPO_ROOT / "metadata" / "MF_RADICAL_PAPER_LEDGER.md"
AUDIT = REPO_ROOT / "GroupApproximation" / "Endpoint" / "MFRadicalPaperAudit.lean"

ROW_RE = re.compile(r"^\|(?P<paper>[^|]+)\|\s*`(?P<decl>[^`]+)`\s*\|(?P<status>[^|]+)\|\s*$")
AUDIT_RE = re.compile(r"^#audit_closed_axioms\s+(?P<decl>\S+)\s*$")
AUDIT_OPEN_RE = re.compile(r"^#audit_axioms\s+(?P<decl>\S+)\s*$")
AUDIT_MACROS = ("#audit_closed_axioms", "#audit_axioms")
DECL_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


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


def audited_decls() -> tuple[list[str], list[str]]:
    """Declarations printed by the paper audit, split by which macro prints them.

    The first list is the closed endpoints (`#audit_closed_axioms`, which also
    rejects a leading binder); the second is those printed with the weaker
    `#audit_axioms`, which permits a displayed hypothesis.

    Any `#audit_*` line this scanner cannot read is a FAILURE, not a skip.
    `AUDIT_RE` wants the declaration on the same line as the macro; Lean also
    accepts it on a continuation line, and accepts a trailing `--` comment.
    Skipping such a line drops the name from `closed`, which silently disables
    failure mode 3 -- "the audit prints a closed endpoint the ledger does not
    list" -- for exactly that name.  The mirror direction always failed loudly,
    so only this one was blind.  Same defect and same fix as
    `check_onesided_transport_ledger.py`.
    """
    if not AUDIT.exists():
        raise SystemExit(f"missing audit file: {AUDIT}")
    closed, opened, malformed = [], [], []
    text = _strip_block_comments(AUDIT.read_text(encoding="utf-8"))
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        macro = next((m for m in AUDIT_MACROS if line.startswith(m)), None)
        if macro is None:
            continue
        rest = line[len(macro):]
        if rest and not rest[0].isspace():
            continue
        rest = rest.split("--", 1)[0].strip()
        tokens = rest.split()
        if len(tokens) != 1 or DECL_TOKEN_RE.fullmatch(tokens[0]) is None:
            malformed.append(
                f"{AUDIT.relative_to(REPO_ROOT)}:{number}: `{macro}` names "
                f"{'no declaration' if not tokens else str(len(tokens)) + ' tokens'}"
                f" on its own line, so this scanner cannot see what it audits;"
                f" put exactly one declaration on the same line as the macro"
            )
            continue
        (closed if macro == "#audit_closed_axioms" else opened).append(tokens[0])
    return closed, opened, malformed


def main() -> int:
    rows = ledger_rows()
    if not rows:
        print("mf-radical ledger: no rows found", file=sys.stderr)
        return 1

    index = build_index()
    closed, opened, malformed = audited_decls()
    failures: list[str] = list(malformed)

    for paper, decl, status in rows:
        if decl not in index:
            failures.append(f"row '{paper}': declaration '{decl}' does not exist")
        if status == "closed":
            if decl not in closed:
                failures.append(
                    f"row '{paper}': claimed closed, but '{decl}' is not printed by "
                    f"#audit_closed_axioms in {AUDIT.relative_to(REPO_ROOT)}"
                )
        elif status == "conditional":
            # A conditional row must be printed with the weaker macro AND must
            # not be printed with the closed one: a statement that passes the
            # binder check is not conditional, and calling it conditional in
            # the ledger would understate what is proved.
            if decl not in opened:
                failures.append(
                    f"row '{paper}': claimed conditional, but '{decl}' is not printed by "
                    f"#audit_axioms in {AUDIT.relative_to(REPO_ROOT)}"
                )
            if decl in closed:
                failures.append(
                    f"row '{paper}': claimed conditional, but '{decl}' passes "
                    f"#audit_closed_axioms, so it is closed"
                )
        else:
            failures.append(
                f"row '{paper}': status '{status}' is neither 'closed' nor 'conditional'"
            )

    listed = {decl for _, decl, _ in rows}
    for decl in closed:
        if decl not in listed:
            failures.append(
                f"audit prints closed endpoint '{decl}' but the ledger does not list it"
            )

    if failures:
        print("mf-radical ledger: FAIL", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1

    n_closed = sum(1 for _, _, st in rows if st == "closed")
    n_cond = len(rows) - n_closed
    print(
        f"mf-radical ledger: OK ({len(rows)} rows audited: "
        f"{n_closed} closed, {n_cond} conditional)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
