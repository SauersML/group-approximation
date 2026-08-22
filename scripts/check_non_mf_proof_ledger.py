#!/usr/bin/env python3
"""Validate the step-level proof ledger for the non-MF manuscript.

`check_non_mf_refs.py` asks whether every margin badge resolves.
`check_non_mf_claim_manifest.py` asks whether every numbered environment has a
manifest entry whose printed statement has not drifted.  Neither asks the
question `metadata/NON_MF_PROOF_LEDGER.md` exists to answer: whether every
inferential step of every printed proof has a Lean counterpart, and whether
that counterpart is the *same* step.

That judgment is human and cannot be automated.  What this gate automates is
the drift around it, so that the judgment stays attached to the text and the
code it was made about:

* the ledger parses, with the two tables in their declared shapes;
* the audited-revision header's three checkable cells -- the manuscript's git
  blob hash, its sha256, and its `wc -l` -- match the file on disk, so a
  manuscript edit cannot land without a deliberate re-pin (`--repin-header`);
* every step cites an anchor that the anchor table declares;
* every `env` anchor's label still exists inside a labelled environment, and
  the printed statement still digests to the recorded value -- the same
  normalization `check_non_mf_claim_manifest.py` uses, so a reworded theorem
  forces the ledger rows about it to be re-read;
* every `sec` and `eq` anchor's label still exists;
* every `prose` anchor's verbatim probe still occurs exactly once in the
  comment-stripped manuscript, so a rewritten paragraph forces the same;
* every Lean declaration named by a step still exists in the tree;
* every `\\leanverified` badge in the manuscript is cited by some step, so a
  newly badged claim cannot enter the manuscript without a ledger row;
* the status vocabulary is respected, and the invariants that make the three
  labels mean what the ledger says they mean are enforced -- an `EXACT`
  statement must cite Lean, a `MISSING` statement must not, and an `EXACT`
  proof requires an `EXACT` statement over literal objects with no
  conditional or literature dependency;
* the summary counts printed in the ledger match the rows.

Exit code is 0 when the ledger is consistent with the manuscript and the tree,
and 1 on any drift.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import build_index


REPO = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO / "non_mf_groups_exist.tex"
DEFAULT_LEDGER = REPO / "metadata" / "NON_MF_PROOF_LEDGER.md"

ROOT_NAMESPACE = "GroupApproximation"
MATHLIB_PREFIX = "Mathlib:"

ANCHOR_KINDS = {"env", "sec", "eq", "prose"}
# A row may name declarations that exist in the tree but whose module has never
# had a green build.  Existence is what `lean_decls` checks; it is not evidence.
# Such a row carries this marker in its note and may not be `EXACT` in either
# column, so a proposed upgrade cannot be mistaken for a completed one while it
# waits for the build.  Drop the marker when the build goes green, then grade.
PENDING_MARKER = "PENDING FIRST GREEN"
# `UNDER-SPECIFIED` is the project-wide fourth mark, adopted from
# `notes/P13_STEP_AUDIT.md`: the printed text is a prose route with no
# determinate step content to bind, and Lean supplies a proof the sentence
# merely gestures at.  `EXACT` would overstate what was checked; `MISMATCH`
# would blame Lean for the manuscript's compression.
STATUSES = ("EXACT", "MISMATCH", "MISSING", "UNDER-SPECIFIED")
OBJECTS = {"literal", "substituted", "-"}
DEPS = {"unconditional", "conditional-data", "literature-input", "open", "-"}
EDITS = {"NO", "YES"}

ANCHOR_HEADER = ["Anchor", "Kind", "Locator", "Digest"]
STEP_HEADER = ["Step", "Anchor", "Claim", "Lean", "Stmt", "Proof", "Obj",
               "Deps", "Source", "Edit", "Note"]
COUNT_HEADER = ["Column", "EXACT", "MISMATCH", "MISSING", "UNDER-SPECIFIED",
                "total"]

ENV_NAMES = ("mainthm", "theorem", "proposition", "lemma", "corollary",
             "definition", "construction", "remark", "figure", "example",
             "fact", "claim")

BEGIN_RE = re.compile(
    r"\\begin\{(?P<env>" + "|".join(ENV_NAMES) + r")\}(?:\[[^\]]*\])?")
LABEL_RE = re.compile(r"\\label\{([^{}]+)\}")
BADGE_RE = re.compile(
    r"\\lean(?P<status>[A-Za-z]+)\s*\{(?P<module>[^{}]+)\}\s*"
    r"\{(?P<declaration>[^{}]+)\}")
COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")
DIGEST_WIDTH = 16


@dataclass(frozen=True)
class Anchor:
    name: str
    kind: str
    locator: str
    digest: str
    row: int


@dataclass(frozen=True)
class Step:
    step_id: str
    anchor: str
    claim: str
    lean: tuple[str, ...]
    statement: str
    proof: str
    objects: str
    deps: str
    source: str
    edit: str
    note: str
    row: int


def strip_comments(source: str) -> str:
    return COMMENT_RE.sub("", source)


def statement_digest(block: str, env: str) -> str:
    """Digest a printed statement exactly as the claim-manifest gate does."""
    body = re.sub(r"^\\begin\{" + re.escape(env) + r"\}(?:\[[^\]]*\])?", "",
                  block)
    body = re.sub(r"\\end\{" + re.escape(env) + r"\}\s*$", "", body)
    body = LABEL_RE.sub("", body)
    body = BADGE_RE.sub("", body)
    return hashlib.sha256(
        re.sub(r"\s+", " ", body).strip().encode("utf-8")).hexdigest()


def environment_digests(source: str) -> dict[str, str]:
    """Map *every* label of every labelled environment to its digest.

    Not only the first.  An environment can carry several semantic labels, and
    a ledger anchor keyed on a later label must resolve to the same statement.
    All labels of one environment therefore share its digest.
    """
    digests: dict[str, str] = {}
    cursor = 0
    while match := BEGIN_RE.search(source, cursor):
        env = match.group("env")
        end_token = f"\\end{{{env}}}"
        end = source.find(end_token, match.end())
        if end < 0:
            cursor = match.end()
            continue
        stop = end + len(end_token)
        block = source[match.start():stop]
        labels = LABEL_RE.findall(block)
        if labels:
            digest = statement_digest(block, env)
            for label in labels:
                digests.setdefault(label, digest)
        cursor = stop
    return digests


def environment_aliases(source: str) -> dict[str, str]:
    """Map each non-first label of a labelled environment to that env's first.

    The first label is the one the claim manifest and the dependency map key
    on, so it is the name a ledger row should quote.  A row keyed on an alias
    still pins correctly, but it is a row waiting to break: the aliases exist
    to be deleted once no draft in flight uses them.
    """
    aliases: dict[str, str] = {}
    cursor = 0
    while match := BEGIN_RE.search(source, cursor):
        env = match.group("env")
        end_token = f"\\end{{{env}}}"
        end = source.find(end_token, match.end())
        if end < 0:
            cursor = match.end()
            continue
        stop = end + len(end_token)
        labels = LABEL_RE.findall(source[match.start():stop])
        for label in labels[1:]:
            aliases.setdefault(label, labels[0])
        cursor = stop
    return aliases


CELL_SPLIT_RE = re.compile(r"(?<!\\)\|")


def split_row(line: str) -> list[str] | None:
    """Split a Markdown table row on unescaped pipes.

    Claims quote mathematics that uses `|` — `|S|`, `|γ|_S`, a presentation
    bar — so the ledger writes those as `\\|` and this undoes the escape.
    """
    stripped = line.strip()
    if not stripped.startswith("|") or not stripped.endswith("|"):
        return None
    inner = stripped[1:-1]
    return [cell.strip().replace("\\|", "|")
            for cell in CELL_SPLIT_RE.split(inner)]


def read_table(text: str, start_marker: str, end_marker: str,
               header: list[str], problems: list[str]) -> list[tuple[int, list[str]]]:
    """Read the pipe table delimited by the two HTML comment markers."""
    begin = text.find(start_marker)
    finish = text.find(end_marker)
    if begin < 0 or finish < 0 or finish < begin:
        problems.append(f"ledger has no {start_marker} … {end_marker} block")
        return []
    offset = text.count("\n", 0, begin) + 1
    body = text[begin + len(start_marker):finish].splitlines()
    rows: list[tuple[int, list[str]]] = []
    seen_header = False
    for index, line in enumerate(body):
        cells = split_row(line)
        if cells is None:
            if line.strip():
                problems.append(
                    f"{start_marker} block, line {offset + index}: not a table row")
            continue
        if not seen_header:
            if cells != header:
                problems.append(
                    f"{start_marker} block: header is {cells}, expected {header}")
            seen_header = True
            continue
        if all(set(cell) <= {"-", ":"} and cell for cell in cells):
            continue
        if len(cells) != len(header):
            problems.append(
                f"{start_marker} block, line {offset + index}: "
                f"{len(cells)} cells, expected {len(header)}")
            continue
        rows.append((offset + index, cells))
    if not seen_header:
        problems.append(f"{start_marker} block has no header row")
    return rows


def unquote(cell: str) -> str:
    return cell.strip().strip("`").strip()


def parse_anchors(text: str, problems: list[str]) -> dict[str, Anchor]:
    anchors: dict[str, Anchor] = {}
    for line, cells in read_table(text, "<!-- LEDGER-ANCHORS -->",
                                  "<!-- END-LEDGER-ANCHORS -->",
                                  ANCHOR_HEADER, problems):
        name, kind, locator, digest = cells
        if not name:
            problems.append(f"line {line}: anchor with empty name")
            continue
        if name in anchors:
            problems.append(f"line {line}: duplicate anchor `{name}`")
            continue
        if kind not in ANCHOR_KINDS:
            problems.append(f"line {line}: anchor `{name}` has invalid kind `{kind}`")
            continue
        locator = unquote(locator)
        if not locator:
            problems.append(f"line {line}: anchor `{name}` has an empty locator")
            continue
        if kind == "env":
            if not re.fullmatch(r"[0-9a-f]{%d}" % DIGEST_WIDTH, digest):
                problems.append(
                    f"line {line}: anchor `{name}` needs a {DIGEST_WIDTH}-hex digest")
                continue
        elif digest != "-":
            problems.append(
                f"line {line}: anchor `{name}` of kind `{kind}` must have digest `-`")
            continue
        anchors[name] = Anchor(name, kind, locator, digest, line)
    return anchors


def parse_steps(text: str, problems: list[str]) -> list[Step]:
    steps: list[Step] = []
    seen: set[str] = set()
    begin = text.find("<!-- LEDGER-STEPS -->")
    finish = text.find("<!-- END-LEDGER-STEPS -->")
    if begin >= 0 and finish > begin:
        offset = text.count("\n", 0, begin) + 1
        for index, raw in enumerate(text[begin:finish].splitlines()):
            if "\\|" in raw:
                problems.append(
                    f"line {offset + index}: escaped `\\|` in a step row.  "
                    "`split_row` understands it, but every other editor of this "
                    "file splits on `|` and silently corrupts the row — that has "
                    "already broken the gate once.  Spell it `card X` for a "
                    "cardinality, `‖x‖` (U+2016) for a norm, `len_S(x)` for a "
                    "word length, and `∣` (U+2223) for a presentation bar")
    for line, cells in read_table(text, "<!-- LEDGER-STEPS -->",
                                  "<!-- END-LEDGER-STEPS -->",
                                  STEP_HEADER, problems):
        (step_id, anchor, claim, lean, statement, proof, objects, deps,
         source, edit, note) = cells
        if not re.fullmatch(r"[A-Z]{2,4}\.[0-9]{2}[a-z]?", step_id):
            problems.append(f"line {line}: malformed step id `{step_id}`")
            continue
        if step_id in seen:
            problems.append(f"line {line}: duplicate step id `{step_id}`")
            continue
        seen.add(step_id)
        if not claim:
            problems.append(f"line {line}: step `{step_id}` has an empty claim")
        declarations: tuple[str, ...] = ()
        if lean != "-":
            declarations = tuple(
                unquote(part) for part in lean.split(";") if unquote(part))
            if not declarations:
                problems.append(
                    f"line {line}: step `{step_id}` has an unreadable Lean cell")
        for field, value, allowed in (
                ("Stmt", statement, set(STATUSES)),
                ("Proof", proof, set(STATUSES)),
                ("Obj", objects, OBJECTS),
                ("Deps", deps, DEPS),
                ("Edit", edit, EDITS)):
            if value not in allowed:
                problems.append(
                    f"line {line}: step `{step_id}` has invalid {field} `{value}`")
        steps.append(Step(step_id, anchor, claim, declarations, statement,
                          proof, objects, deps, source, edit, note, line))
    return steps


def full_name(declaration: str) -> str:
    if declaration.startswith(f"{ROOT_NAMESPACE}."):
        return declaration
    return f"{ROOT_NAMESPACE}.{declaration}"


def check_anchors(anchors: dict[str, Anchor], tex_source: str,
                  problems: list[str]) -> None:
    labels = set(LABEL_RE.findall(tex_source))
    digests = environment_digests(tex_source)
    aliases = environment_aliases(tex_source)
    normalized = re.sub(r"\s+", " ", tex_source)
    for anchor in anchors.values():
        where = f"line {anchor.row}: anchor `{anchor.name}`"
        if anchor.kind in ("env", "sec", "eq"):
            if anchor.locator not in labels:
                problems.append(
                    f"{where}: no \\label{{{anchor.locator}}} in the manuscript")
                continue
        if anchor.kind == "env":
            if anchor.locator in aliases:
                problems.append(
                    f"{where}: \\label{{{anchor.locator}}} is a legacy alias of "
                    f"\\label{{{aliases[anchor.locator]}}} on the same "
                    "environment; key the anchor on the primary label, which is "
                    "what the claim manifest and the dependency map use")
            actual = digests.get(anchor.locator)
            if actual is None:
                problems.append(
                    f"{where}: \\label{{{anchor.locator}}} is not inside a "
                    "labelled environment")
            elif actual[:DIGEST_WIDTH] != anchor.digest:
                problems.append(
                    f"{where}: printed statement changed "
                    f"({anchor.digest} -> {actual[:DIGEST_WIDTH]}); "
                    "re-read every step on this anchor before updating it")
        elif anchor.kind == "prose":
            if "|" in anchor.locator:
                problems.append(f"{where}: prose probe may not contain `|`")
                continue
            probe = re.sub(r"\s+", " ", anchor.locator)
            count = normalized.count(probe)
            if count != 1:
                problems.append(
                    f"{where}: prose probe occurs {count} times, expected once")


def check_steps(steps: list[Step], anchors: dict[str, Anchor],
                index: dict[str, Path], problems: list[str]) -> None:
    for step in steps:
        where = f"line {step.row}: step `{step.step_id}`"
        if step.anchor not in anchors:
            problems.append(f"{where}: unknown anchor `{step.anchor}`")
        for declaration in step.lean:
            if declaration.startswith(MATHLIB_PREFIX):
                continue
            if full_name(declaration) not in index:
                problems.append(
                    f"{where}: no declaration {full_name(declaration)} in the tree")
        if step.statement == "EXACT" and not step.lean:
            problems.append(f"{where}: an EXACT statement must cite a declaration")
        if step.statement == "MISSING" and step.lean \
                and step.deps == "unconditional":
            problems.append(
                f"{where}: a MISSING statement that cites a declaration must "
                "record why the declaration does not establish it")
        if step.statement == "UNDER-SPECIFIED" and not step.lean:
            problems.append(
                f"{where}: an UNDER-SPECIFIED statement must cite the declaration "
                "standing where the prose gestures")
        if step.proof == "UNDER-SPECIFIED":
            if step.statement not in ("EXACT", "UNDER-SPECIFIED"):
                problems.append(
                    f"{where}: an UNDER-SPECIFIED proof requires an EXACT or "
                    "UNDER-SPECIFIED statement — there is nothing to under-specify "
                    "against otherwise")
            if not step.lean:
                problems.append(
                    f"{where}: an UNDER-SPECIFIED proof must cite the declaration "
                    "standing where the prose gestures")
        if step.proof == "EXACT":
            if step.statement == "MISSING":
                problems.append(
                    f"{where}: an EXACT proof requires a stated Lean counterpart")
            if step.objects != "literal":
                problems.append(
                    f"{where}: an EXACT proof requires literal objects")
            if step.deps not in ("unconditional", "open"):
                problems.append(
                    f"{where}: an EXACT proof cannot depend on `{step.deps}`")
        if step.statement == "MISSING" and step.proof == "EXACT":
            problems.append(
                f"{where}: a MISSING statement cannot have an EXACT proof")
        if PENDING_MARKER in step.note and "EXACT" in (step.statement, step.proof):
            problems.append(
                f"{where}: a row marked `{PENDING_MARKER}` cannot be EXACT — the "
                "declarations it names have not been through a green build, so "
                "nothing about them has been established yet")
        if step.objects == "-" and "EXACT" in (step.statement, step.proof):
            problems.append(
                f"{where}: an EXACT cell requires a recorded object identity")


def check_badge_coverage(steps: list[Step], tex_source: str,
                         index: dict[str, Path], problems: list[str]) -> None:
    cited = {full_name(declaration) for step in steps
             for declaration in step.lean
             if not declaration.startswith(MATHLIB_PREFIX)}
    for match in BADGE_RE.finditer(tex_source):
        if match.group("status") != "verified":
            continue
        declaration = match.group("declaration").strip()
        line = tex_source.count("\n", 0, match.start()) + 1
        if full_name(declaration) not in index:
            problems.append(
                f"{DEFAULT_TEX.name}:{line}: badge names {declaration}, "
                "which is not in the tree")
        if full_name(declaration) not in cited:
            problems.append(
                f"{DEFAULT_TEX.name}:{line}: badge {declaration} has no ledger row")


def check_counts(text: str, steps: list[Step], problems: list[str]) -> None:
    rows = read_table(text, "<!-- LEDGER-COUNTS -->",
                      "<!-- END-LEDGER-COUNTS -->", COUNT_HEADER, problems)
    actual = {
        "statement": [sum(step.statement == status for step in steps)
                      for status in STATUSES],
        "proof": [sum(step.proof == status for step in steps)
                  for status in STATUSES],
    }
    declared: set[str] = set()
    for line, cells in rows:
        column, *values = cells
        declared.add(column)
        if column not in actual:
            problems.append(f"line {line}: unknown count row `{column}`")
            continue
        try:
            numbers = [int(value) for value in values]
        except ValueError:
            problems.append(f"line {line}: count row `{column}` is not numeric")
            continue
        expected = actual[column] + [len(steps)]
        if numbers != expected:
            problems.append(
                f"line {line}: count row `{column}` says {numbers}, "
                f"rows say {expected}")
    for column in actual:
        if column not in declared:
            problems.append(f"the count table has no `{column}` row")


ANCHOR_ROW_RE = re.compile(
    r"^\|\s*(?P<name>[^|]+?)\s*\|\s*env\s*\|\s*(?P<label>[^|]+?)\s*\|\s*"
    r"(?P<digest>[0-9a-f]{%d})\s*\|$" % DIGEST_WIDTH)

# The audited-revision header of the ledger.  Three of its four cells are
# recomputable from the manuscript file alone and are therefore checkable; the
# `commit` cell names a commit by description and stays human.  The header
# went stale twice in two days while nothing validated it, so these three rows
# are now a gate, not documentation.
HEADER_BLOB_RE = re.compile(
    r"^\|\s*`git hash-object [^`|]*`\s*\|\s*`(?P<hex>[0-9a-f]{40})`\s*\|\s*$",
    re.MULTILINE)
HEADER_SHA256_RE = re.compile(
    r"^\|\s*sha256 of the file\s*\|\s*`(?P<hex>[0-9a-f]{64})`\s*\|\s*$",
    re.MULTILINE)
HEADER_WC_RE = re.compile(
    r"^\|\s*`wc -l`\s*\|\s*(?P<count>\d+)\s*\|\s*$", re.MULTILINE)


def header_actuals(tex: Path) -> tuple[str, str, int]:
    """The three checkable header values, recomputed from the file's bytes.

    The blob hash is `git hash-object` without git: sha1 over the object
    header `blob <size>\\0` followed by the raw bytes.  The line count is the
    newline count, which is what `wc -l` reports.
    """
    data = tex.read_bytes()
    blob = hashlib.sha1(b"blob %d\x00" % len(data) + data).hexdigest()
    return blob, hashlib.sha256(data).hexdigest(), data.count(b"\n")


def check_header_pin(tex: Path, ledger_text: str, problems: list[str]) -> None:
    """Fail when the audited-revision header disagrees with the file on disk.

    A mismatch means the manuscript moved without a re-pin, and every row
    below the header is then unciteable until someone re-reads the rows the
    edit touched and refreshes the header (`--repin-header`).  A header with a
    missing checkable row is reported too: deleting the pin must not silence
    the gate.
    """
    blob_m = HEADER_BLOB_RE.search(ledger_text)
    sha_m = HEADER_SHA256_RE.search(ledger_text)
    wc_m = HEADER_WC_RE.search(ledger_text)
    if blob_m is None or sha_m is None or wc_m is None:
        problems.append(
            "header pin: the audited-revision table is missing one of its "
            "three checkable rows (git blob, sha256, `wc -l`); without them "
            "the rows below cannot be read as current")
        return
    blob, sha, count = header_actuals(tex)
    if blob_m.group("hex") != blob:
        problems.append(
            f"header pin: ledger pins tex blob `{blob_m.group('hex')}` but "
            f"the file is `{blob}` -- the manuscript moved without a re-pin; "
            f"re-read the rows the edit touched, then run --repin-header")
    if sha_m.group("hex") != sha:
        problems.append(
            f"header pin: ledger pins sha256 `{sha_m.group('hex')[:12]}...` "
            f"but the file is `{sha[:12]}...`; run --repin-header after "
            f"re-reading the rows the edit touched")
    if int(wc_m.group("count")) != count:
        problems.append(
            f"header pin: ledger pins `wc -l` {wc_m.group('count')} but the "
            f"file has {count} lines; run --repin-header after re-reading "
            f"the rows the edit touched")


def repin_header(tex: Path, ledger: Path) -> list[str]:
    """Refresh the three checkable header cells to the file on disk.

    Deliberate and logged, like `repin`: refreshing the header asserts that
    the rows have been re-read against the manuscript as it now stands, so it
    must never happen as a side effect of checking.  The `commit` cell is not
    touched -- it names a commit by description, which cannot be recomputed.
    """
    blob, sha, count = header_actuals(tex)
    text = ledger.read_text(encoding="utf-8")
    changed: list[str] = []

    def sub_hex(regex: re.Pattern[str], value: str, label: str,
                text: str) -> str:
        match = regex.search(text)
        if match is None or match.group(1) == value:
            return text
        changed.append(f"{label}: {match.group(1)} -> {value}")
        return text[:match.start(1)] + value + text[match.end(1):]

    text = sub_hex(HEADER_BLOB_RE, blob, "blob", text)
    text = sub_hex(HEADER_SHA256_RE, sha, "sha256", text)
    text = sub_hex(HEADER_WC_RE, str(count), "wc -l", text)
    if changed:
        ledger.write_text(text, encoding="utf-8")
    return changed


def repin(tex: Path, ledger: Path) -> tuple[int, list[str]]:
    """Rewrite `env` anchor digests to the manuscript's current statements.

    Re-pinning is deliberate and logged, never a side effect of checking: a
    changed digest means a printed statement was reworded, and the rows on that
    anchor have to be re-read before the new digest is trusted.  Prose probes
    are content, not fingerprints, so they are never rewritten -- a moved
    paragraph still fails loudly.
    """
    source = strip_comments(tex.read_text(encoding="utf-8"))
    digests = environment_digests(source)
    lines = ledger.read_text(encoding="utf-8").split("\n")
    changed: list[str] = []
    for index, line in enumerate(lines):
        match = ANCHOR_ROW_RE.match(line)
        if match is None:
            continue
        actual = digests.get(match.group("label"))
        if actual is None or actual[:DIGEST_WIDTH] == match.group("digest"):
            continue
        changed.append(f"{match.group('name')}: {match.group('digest')} -> "
                       f"{actual[:DIGEST_WIDTH]}")
        lines[index] = (f"| {match.group('name')} | env | "
                        f"{match.group('label')} | {actual[:DIGEST_WIDTH]} |")
    if changed:
        ledger.write_text("\n".join(lines), encoding="utf-8")
    return len(changed), changed


def validate(repo: Path, tex: Path, ledger: Path,
             require_header: bool = True) -> list[str]:
    problems: list[str] = []
    try:
        ledger_text = ledger.read_text(encoding="utf-8")
    except OSError as error:
        return [f"cannot read {ledger}: {error}"]
    if require_header:
        check_header_pin(tex, ledger_text, problems)
    try:
        tex_source = strip_comments(tex.read_text(encoding="utf-8"))
    except OSError as error:
        return [f"cannot read {tex}: {error}"]

    anchors = parse_anchors(ledger_text, problems)
    steps = parse_steps(ledger_text, problems)
    index = build_index(repo)

    check_anchors(anchors, tex_source, problems)
    check_steps(steps, anchors, index, problems)
    check_badge_coverage(steps, tex_source, index, problems)
    check_counts(ledger_text, steps, problems)

    used = {step.anchor for step in steps}
    for name in sorted(set(anchors) - used):
        problems.append(f"anchor `{name}` is declared but no step uses it")
    return problems


REREAD_MARKERS = ("printed statement changed", "prose probe occurs")


def is_reread(problem: str) -> bool:
    """Is this drift under a concurrent edit rather than outright breakage?

    Ten sessions share this checkout, so the manuscript moves while the ledger is
    read.  A moved statement or a relocated paragraph is not a broken ledger — it
    is a demand to re-read the rows on that anchor.  A missing label, a missing
    declaration or a violated invariant is breakage and is reported separately.
    """
    return any(marker in problem for marker in REREAD_MARKERS)


def summarize(steps: list[Step]) -> str:
    def counts(field: str) -> str:
        return ", ".join(
            f"{sum(getattr(step, field) == status for step in steps)} {status}"
            for status in STATUSES)
    return (f"{len(steps)} steps; statement: {counts('statement')}; "
            f"proof: {counts('proof')}")


LEDGER_TEMPLATE = """# demo ledger

<!-- LEDGER-COUNTS -->
| Column | EXACT | MISMATCH | MISSING | UNDER-SPECIFIED | total |
| --- | --- | --- | --- | --- | --- |
| statement | 1 | 0 | 0 | 0 | 1 |
| proof | 1 | 0 | 0 | 0 | 1 |
<!-- END-LEDGER-COUNTS -->

<!-- LEDGER-ANCHORS -->
| Anchor | Kind | Locator | Digest |
| --- | --- | --- | --- |
| thm:demo | env | thm:demo | {digest} |
<!-- END-LEDGER-ANCHORS -->

<!-- LEDGER-STEPS -->
| Step | Anchor | Claim | Lean | Stmt | Proof | Obj | Deps | Source | Edit | Note |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| DM.01 | thm:demo | True holds | `demo_exact` | EXACT | EXACT | literal | unconditional | - | NO | - |
<!-- END-LEDGER-STEPS -->
"""


def self_test() -> int:
    # `split_row` still has to understand `\|`: a ledger written before the
    # escape was banned must keep parsing, so that the gate can report the ban
    # rather than a cell-count error nobody can act on.
    if split_row(r"| a | card \| S \| | b |") != ["a", "card | S |", "b"]:
        print("self-test: split_row no longer understands an escaped pipe",
              file=sys.stderr)
        return 1
    with tempfile.TemporaryDirectory() as directory:
        repo = Path(directory)
        module = repo / "GroupApproximation" / "Demo"
        module.mkdir(parents=True)
        (module / "Exact.lean").write_text(
            "namespace GroupApproximation\n"
            "theorem demo_exact : True := by trivial\n"
            "end GroupApproximation\n", encoding="utf-8")
        tex = repo / "paper.tex"
        tex.write_text(
            "\\begin{theorem}[Demo]\\label{thm:demo}\nTrue.\n"
            "\\leanverified{Demo/Exact}{GroupApproximation.demo_exact}\n"
            "\\end{theorem}\n", encoding="utf-8")
        source = strip_comments(tex.read_text(encoding="utf-8"))
        digest = environment_digests(source)["thm:demo"][:DIGEST_WIDTH]
        ledger = repo / "ledger.md"
        good = LEDGER_TEMPLATE.format(digest=digest)
        ledger.write_text(good, encoding="utf-8")
        if problems := validate(repo, tex, ledger, require_header=False):
            print(f"self-test rejected a valid ledger: {problems}", file=sys.stderr)
            return 1

        cases = [
            ("statement drift",
             good.replace(digest, "0" * DIGEST_WIDTH), "printed statement changed"),
            ("missing declaration",
             good.replace("`demo_exact`", "`demo_absent`"),
             "no declaration GroupApproximation.demo_absent"),
            ("uncovered badge",
             good.replace("| `demo_exact` | EXACT | EXACT | literal | unconditional",
                          "| - | MISSING | MISSING | - | open"),
             "has no ledger row"),
            ("EXACT proof over a MISSING statement",
             good.replace("| EXACT | EXACT | literal", "| MISSING | EXACT | literal"),
             "an EXACT proof requires a stated Lean counterpart"),
            ("unexplained MISSING statement citing Lean",
             good.replace("| EXACT | EXACT | literal", "| MISSING | MISSING | literal"),
             "must record why the declaration does not establish it"),
            ("escaped pipes are rejected in a step row",
             good.replace("True holds", r"card \| S \| is positive"),
             "escaped `\\|` in a step row"),
            ("EXACT proof on conditional data",
             good.replace("| unconditional |", "| conditional-data |"),
             "cannot depend on `conditional-data`"),
            ("EXACT proof over substituted objects",
             good.replace("| literal |", "| substituted |"),
             "requires literal objects"),
            ("stale counts",
             good.replace("| statement | 1 | 0 | 0 | 0 | 1 |",
                          "| statement | 0 | 1 | 0 | 0 | 1 |"),
             "count row `statement`"),
            ("UNDER-SPECIFIED statement with no declaration",
             good.replace("| `demo_exact` | EXACT | EXACT",
                          "| - | UNDER-SPECIFIED | MISSING"),
             "must cite the declaration standing where the prose gestures"),
            ("UNDER-SPECIFIED proof over a MISSING statement",
             good.replace("| EXACT | EXACT | literal",
                          "| MISSING | UNDER-SPECIFIED | literal"),
             "nothing to under-specify against"),
            ("unknown anchor",
             good.replace("| DM.01 | thm:demo |", "| DM.01 | thm:ghost |"),
             "unknown anchor `thm:ghost`"),
            ("invalid status",
             good.replace("| EXACT | EXACT | literal", "| PARTIAL | EXACT | literal"),
             "invalid Stmt `PARTIAL`"),
            ("EXACT on a row still waiting for a green build",
             good.replace("| NO | - |", "| NO | PENDING FIRST GREEN: proposed |"),
             "cannot be EXACT"),
            ("duplicate step id",
             good.replace(
                 "<!-- END-LEDGER-STEPS -->",
                 "| DM.01 | thm:demo | again | - | MISSING | MISSING | - | open "
                 "| - | NO | - |\n<!-- END-LEDGER-STEPS -->"),
             "duplicate step id"),
        ]
        for name, mutated, expected in cases:
            ledger.write_text(mutated, encoding="utf-8")
            found = validate(repo, tex, ledger, require_header=False)
            if expected is None:
                if found:
                    print(f"self-test rejected {name}: {found}", file=sys.stderr)
                    return 1
                continue
            if not any(expected in problem for problem in found):
                print(f"self-test missed {name}: {found}", file=sys.stderr)
                return 1

        # A prose anchor must occur exactly once.
        tex.write_text(
            "\\begin{theorem}[Demo]\\label{thm:demo}\nTrue.\n"
            "\\leanverified{Demo/Exact}{GroupApproximation.demo_exact}\n"
            "\\end{theorem}\nA repeated phrase. A repeated phrase.\n",
            encoding="utf-8")
        source = strip_comments(tex.read_text(encoding="utf-8"))
        digest = environment_digests(source)["thm:demo"][:DIGEST_WIDTH]
        prose = LEDGER_TEMPLATE.format(digest=digest).replace(
            "<!-- END-LEDGER-ANCHORS -->",
            "| p:demo | prose | `A repeated phrase.` | - |\n"
            "<!-- END-LEDGER-ANCHORS -->").replace(
            "<!-- END-LEDGER-STEPS -->",
            "| DM.02 | p:demo | repeated | - | MISSING | MISSING | - | open "
            "| - | NO | - |\n<!-- END-LEDGER-STEPS -->").replace(
            "| statement | 1 | 0 | 0 | 0 | 1 |",
            "| statement | 1 | 0 | 1 | 0 | 2 |").replace(
            "| proof | 1 | 0 | 0 | 0 | 1 |",
            "| proof | 1 | 0 | 1 | 0 | 2 |")
        ledger.write_text(prose, encoding="utf-8")
        found = validate(repo, tex, ledger, require_header=False)
        if not any("prose probe occurs 2 times" in problem for problem in found):
            print(f"self-test missed prose drift: {found}", file=sys.stderr)
            return 1

        # A second label on the same environment is an alias: it digests to the
        # same statement, so the anchor still pins and `repin` can still move
        # it, but keying a row on it is reported so that deleting the alias
        # cannot quietly orphan the row.
        tex.write_text(
            "\\begin{theorem}[Demo]\\label{thm:demo}\\label{thm:alias}\nTrue.\n"
            "\\leanverified{Demo/Exact}{GroupApproximation.demo_exact}\n"
            "\\end{theorem}\n", encoding="utf-8")
        source = strip_comments(tex.read_text(encoding="utf-8"))
        table = environment_digests(source)
        if table.get("thm:alias") != table.get("thm:demo"):
            print("self-test: an alias label did not inherit its statement "
                  f"digest: {table}", file=sys.stderr)
            return 1
        digest = table["thm:alias"][:DIGEST_WIDTH]
        aliased = LEDGER_TEMPLATE.format(digest=digest).replace(
            "| thm:demo | env | thm:demo |", "| thm:demo | env | thm:alias |")
        ledger.write_text(aliased, encoding="utf-8")
        found = validate(repo, tex, ledger, require_header=False)
        if not any("is a legacy alias of" in problem for problem in found):
            print(f"self-test missed an aliased anchor: {found}", file=sys.stderr)
            return 1
        if any("not inside a labelled environment" in problem
               or "printed statement changed" in problem for problem in found):
            print("self-test: an aliased anchor was reported as unpinned rather "
                  f"than as an alias: {found}", file=sys.stderr)
            return 1

        # The header pin: three checkable cells against the file on disk.  A
        # matching header passes, a tampered blob fails loudly, a deleted
        # header fails loudly, and `repin_header` restores a stale one.
        blob, sha, count = header_actuals(tex)
        header = (f"| `git hash-object non_mf_groups_exist.tex` | `{blob}` |\n"
                  f"| sha256 of the file | `{sha}` |\n"
                  f"| `wc -l` | {count} |\n\n")
        digest = environment_digests(
            strip_comments(tex.read_text(encoding="utf-8")))
        pinned = header + LEDGER_TEMPLATE.format(
            digest=digest["thm:demo"][:DIGEST_WIDTH])
        ledger.write_text(pinned, encoding="utf-8")
        if problems := validate(repo, tex, ledger):
            print(f"self-test rejected a pinned ledger: {problems}",
                  file=sys.stderr)
            return 1
        ledger.write_text(pinned.replace(blob, "0" * 40), encoding="utf-8")
        found = validate(repo, tex, ledger)
        if not any("header pin: ledger pins tex blob" in p for p in found):
            print(f"self-test missed a stale header blob: {found}",
                  file=sys.stderr)
            return 1
        ledger.write_text(
            LEDGER_TEMPLATE.format(digest=digest["thm:demo"][:DIGEST_WIDTH]),
            encoding="utf-8")
        found = validate(repo, tex, ledger)
        if not any("missing one of its three checkable rows" in p
                   for p in found):
            print(f"self-test missed a deleted header: {found}",
                  file=sys.stderr)
            return 1
        ledger.write_text(pinned.replace(blob, "0" * 40), encoding="utf-8")
        if not repin_header(tex, ledger):
            print("self-test: repin_header refreshed nothing on a stale header",
                  file=sys.stderr)
            return 1
        if problems := validate(repo, tex, ledger):
            print(f"self-test: repin_header left problems: {problems}",
                  file=sys.stderr)
            return 1
    print("non-MF proof ledger: self-test passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=REPO)
    parser.add_argument("--tex", type=Path, default=DEFAULT_TEX)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument(
        "--repin-digests", action="store_true",
        help="rewrite env anchor digests to the manuscript's current statements; "
             "use only after re-reading the rows on every anchor it reports")
    parser.add_argument(
        "--repin-header", action="store_true",
        help="refresh the three checkable audited-revision header cells (git "
             "blob, sha256, `wc -l`) to the manuscript on disk; use only after "
             "re-reading the rows the manuscript edit touched")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()

    tex = args.tex if args.tex.is_absolute() else args.repo / args.tex
    ledger = args.ledger if args.ledger.is_absolute() else args.repo / args.ledger
    if args.repin_digests:
        count, changed = repin(tex, ledger)
        for entry in changed:
            print(f"repinned {entry}")
        print(f"check-non-mf-proof-ledger: repinned {count} anchor digest(s)")
    if args.repin_header:
        for entry in repin_header(tex, ledger):
            print(f"repinned header {entry}")
    problems = validate(args.repo, tex, ledger)
    if problems:
        reread = [p for p in problems if is_reread(p)]
        broken = [p for p in problems if not is_reread(p)]
        print(f"check-non-mf-proof-ledger: {len(problems)} problem(s):",
              file=sys.stderr)
        if broken:
            print("  -- broken: an anchor, a declaration or an invariant is gone",
                  file=sys.stderr)
            for problem in broken:
                print(f"    {problem}", file=sys.stderr)
        if reread:
            print("  -- drifted: the manuscript moved under the ledger.  Re-read the "
                  "rows on each anchor\n     below, then re-pin with --repin-digests "
                  "or repoint the probe by hand.", file=sys.stderr)
            for problem in reread:
                print(f"    {problem}", file=sys.stderr)
        return 1

    ledger_text = ledger.read_text(encoding="utf-8")
    steps = parse_steps(ledger_text, [])
    anchors = parse_anchors(ledger_text, [])
    print(f"check-non-mf-proof-ledger: {len(anchors)} anchors, "
          f"{summarize(steps)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
