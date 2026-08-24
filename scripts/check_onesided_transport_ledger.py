#!/usr/bin/env python3
"""Gate the one-sided-transport ledger against the Lean development.

This is `scripts/check_mf_radical_ledger.py` pointed at
`metadata/ONESIDED_TRANSPORT_LEDGER.md` and
`GroupApproximation/Endpoint/OneSidedTransportAudit.lean`, with one extra
failure mode that the MF-radical package does not need: this manuscript is
still being edited, so a numbered statement can appear in the `.tex` without
anyone noticing that no row covers it.

Four failure modes are checked, all of them silent otherwise:

1. the ledger names a declaration that does not exist (a rename, or a row that
   was aspirational when written);
2. the ledger names a declaration that the audit does not print, so nothing
   checks its axiom closure or its zero-input status;
3. the audit prints a closed endpoint that the ledger does not list, so the
   advertised surface is larger than the ledger admits;
4. the manuscript carries a `\\label` that no row mentions, so a printed
   statement has no ledger entry at all.

A `MISSING` row is the ledger's way of saying that a printed statement has no
proof.  Such a row still names its intended target, and two things are checked
about it: the audit must not print that name under either macro, and the name
must not have become a `theorem`.  Either would mean the row is stale in the
direction that flatters the development.

This is a lexical check, like the other manuscript gates: it resolves names
against `lean_decls.build_index`, which tracks the namespace stack rather than
elaborating.  That is enough for the failures it guards against.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import DECL_RE, _strip_block_comments, build_index  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
LEDGER = REPO_ROOT / "metadata" / "ONESIDED_TRANSPORT_LEDGER.md"
AUDIT = REPO_ROOT / "GroupApproximation" / "Endpoint" / "OneSidedTransportAudit.lean"
MANUSCRIPT = REPO_ROOT / "non_mf_groups_exist.tex"

ROW_RE = re.compile(r"^\|(?P<paper>[^|]+)\|\s*`(?P<decl>[^`]+)`\s*\|(?P<status>[^|]+)\|\s*$")
AUDIT_RE = re.compile(r"^#audit_closed_axioms\s+(?P<decl>\S+)\s*$")
AUDIT_OPEN_RE = re.compile(r"^#audit_axioms\s+(?P<decl>\S+)\s*$")
LABEL_RE = re.compile(r"\\label\{(?P<label>[^}]+)\}")

STATUSES = ("closed", "conditional", "MISSING")

# Section labels are cross-reference anchors, not printed statements.
LABEL_SKIP_PREFIXES = ("sec:", "fig:", "tab:")


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
    """Declarations printed by the audit, split by which macro prints them.

    The first list is the closed endpoints (`#audit_closed_axioms`, which also
    rejects a leading binder); the second is those printed with the weaker
    `#audit_axioms`, which permits a displayed hypothesis or a statement over
    caller-supplied data.
    """
    if not AUDIT.exists():
        raise SystemExit(f"missing audit file: {AUDIT}")
    closed, opened = [], []
    for line in AUDIT.read_text(encoding="utf-8").splitlines():
        m = AUDIT_RE.match(line.strip())
        if m:
            closed.append(m.group("decl"))
            continue
        m = AUDIT_OPEN_RE.match(line.strip())
        if m:
            opened.append(m.group("decl"))
    return closed, opened


def manuscript_labels() -> list[str]:
    if not MANUSCRIPT.exists():
        raise SystemExit(f"missing manuscript: {MANUSCRIPT}")
    text = MANUSCRIPT.read_text(encoding="utf-8")
    labels = []
    for m in LABEL_RE.finditer(text):
        label = m.group("label")
        if label.startswith(LABEL_SKIP_PREFIXES):
            continue
        if label not in labels:
            labels.append(label)
    return labels


def declaration_keyword(name: str, path: Path) -> str | None:
    """The keyword introducing `name` in `path`, or `None` if not found.

    `lean_decls.build_index` records where a declaration lives but not how it
    was introduced.  A `MISSING` row needs the difference: its target is
    allowed to exist as a `def ... : Prop`, and is not allowed to be a
    `theorem`, which would mean the row is stale.
    """
    tail = name.rsplit(".", 1)[-1]
    text = _strip_block_comments(path.read_text(encoding="utf-8"))
    for raw in text.splitlines():
        line = raw.split("--", 1)[0].rstrip()
        if not line or line[0].isspace():
            continue
        m = DECL_RE.match(line)
        if m and m.group("name") == tail:
            return m.group("kw")
    return None


def main() -> int:
    rows = ledger_rows()
    if not rows:
        print("one-sided-transport ledger: no rows found", file=sys.stderr)
        return 1

    index = build_index()
    closed, opened = audited_decls()
    failures: list[str] = []

    for paper, decl, status in rows:
        if status not in STATUSES:
            failures.append(
                f"row '{paper}': status '{status}' is not one of {', '.join(STATUSES)}"
            )
            continue

        if status == "MISSING":
            # The row asserts that nothing proves this statement.  The audit
            # must not advertise the name, and the name must not have quietly
            # become a proof.
            if decl in closed or decl in opened:
                failures.append(
                    f"row '{paper}': marked MISSING, but '{decl}' is printed in "
                    f"{AUDIT.relative_to(REPO_ROOT)}"
                )
            path = index.get(decl)
            if path is not None:
                kw = declaration_keyword(decl, path)
                if kw in ("theorem", "lemma"):
                    failures.append(
                        f"row '{paper}': marked MISSING, but '{decl}' is a {kw} in "
                        f"{path.relative_to(REPO_ROOT)}; the row is stale"
                    )
            continue

        if decl not in index:
            failures.append(f"row '{paper}': declaration '{decl}' does not exist")

        if status == "closed":
            if decl not in closed:
                failures.append(
                    f"row '{paper}': claimed closed, but '{decl}' is not printed by "
                    f"#audit_closed_axioms in {AUDIT.relative_to(REPO_ROOT)}"
                )
        else:
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

    listed = {decl for _, decl, _ in rows}
    for decl in closed:
        if decl not in listed:
            failures.append(
                f"audit prints closed endpoint '{decl}' but the ledger does not list it"
            )

    papers = "\n".join(paper for paper, _, _ in rows)
    for label in manuscript_labels():
        if label not in papers:
            failures.append(
                f"manuscript label '{label}' has no row in "
                f"{LEDGER.relative_to(REPO_ROOT)}"
            )

    if failures:
        print("one-sided-transport ledger: FAIL", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1

    counts = {status: sum(1 for _, _, st in rows if st == status) for status in STATUSES}
    missing = [paper for paper, _, st in rows if st == "MISSING"]
    print(
        f"one-sided-transport ledger: OK ({len(rows)} rows audited: "
        f"{counts['closed']} closed, {counts['conditional']} conditional, "
        f"{counts['MISSING']} MISSING)"
    )
    for paper in missing:
        print(f"  MISSING: {paper}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
