#!/usr/bin/env python3
"""Census of the manuscripts' DISPLAYS, the half `sentence_census.py` skips.

`scripts/sentence_census.py` deletes display material before it splits prose
into sentences, and it is right to: a matrix dropped into a sentence is noise,
and the sentence around a display is where the assertion is usually graded.
The cost is that the displays themselves are ungraded.  An external 1:1 audit
counted 67 top-level display blocks across the two manuscripts that no gate
reads, including a table entry the recognition paper's compiler section relies
on.  This script grades them.

It is a **sibling** of `sentence_census.py`, not an extension of it, and that is
deliberate: the sentence keys are the sha256 of the extracted sentence text, so
any change to `extract()` re-keys all 227 non-MF sentences at once.  This file
imports the shared lexical helpers and leaves that function alone.

    scripts/display_census.py                  regenerate the census
    scripts/display_census.py --summary        print the counts and stop
    scripts/display_census.py --check          fail on any unassigned display
    scripts/display_census.py --verify-decls   check that every named decl exists
    scripts/display_census.py --verify-links   the two integrity cross-checks

## What counts as one row

One row per **top-level** display block: an `equation`/`align`/`gather`/
`multline`/`tabular`/... environment, or an unnumbered `\\[ … \\]` or `$$ … $$`,
whose enclosing environment is not itself a display.  A nested `pmatrix` inside
an `align` is part of its block, not a row of its own.

An `align` with several `\\\\`-separated lines is ONE row.  Splitting on `\\\\`
would key each line by its position in the block, and a realignment that moves a
line would silently expire its assignment; the printed assertion is the block.
The exception is a line the prose references individually: if a `\\label` inside
the block is `\\eqref`-ed anywhere in the manuscript, that line also gets its own
row, keyed by the LABEL rather than by the content, because a label is stable
under rewording and a line position is not.

## The key

For a block row, the first twelve hex digits of the sha256 of the normalized
block body, with an occurrence counter appended inside one anchor when the same
body occurs twice (the same rule `sentence_census.py` uses, for the same
reason).  For a sub-labelled row, the first twelve hex digits of the sha256 of
the label, so that editing the line does not move the row.

## The grades

| status | meaning |
| --- | --- |
| `carrier` | `decls` names declarations that state this displayed identity |
| `notation-only` | the display defines a symbol the prose introduces; it asserts nothing |
| `derivation-of:<key>` | an intermediate step of a proof whose conclusion is graded at that SENTENCE key |
| `unassigned` | not yet triaged --- the state `--check` rejects |

`derivation-of` carries no declarations: the point of the grade is that the step
is *not* separately stated in Lean, and naming a declaration on it would be the
same overreach the sentence census's `formalized` rule forbids.  Its target must
resolve in the sentence census and must not itself be unassigned, or the row
would defer to a grade nobody made.  That is one of the two `--verify-links`
checks; the other is that every `\\label` the prose `\\eqref`-es has a row.

## Not a scoreboard

The same rule as the sentence map: a `carrier` row names a declaration that
already earns its place.  Writing a declaration in order to fill a row turns a
gate green without adding knowledge.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

import sentence_census as sc  # noqa: E402  (path set above)

DEFAULT_TEX = os.path.join(ROOT, "non_mf_groups_exist.tex")
DEFAULT_MAP = os.path.join(ROOT, "metadata", "NON_MF_DISPLAY_MAP.tsv")
DEFAULT_OUT = os.path.join(ROOT, "metadata", "NON_MF_DISPLAY_CENSUS.tsv")
DEFAULT_OUT_MD = os.path.join(ROOT, "metadata", "NON_MF_DISPLAY_CENSUS.md")
DEFAULT_SENTENCE_CENSUS = os.path.join(
    ROOT, "metadata", "NON_MF_SENTENCE_CENSUS.tsv")

TEX_LABEL = "non_mf_groups_exist.tex"
MAP_LABEL = "metadata/NON_MF_DISPLAY_MAP.tsv"

VALID_STATUSES = {"carrier", "notation-only"}
DERIVATION = re.compile(r"^derivation-of:([0-9a-f]{12})$")

# `sentence_census` removes structural environments as well as mathematical
# displays.  A bibliography is prose metadata, not a displayed assertion, so
# it must not become a display-census row merely because the sentence lexer
# skips it.
AUDITED_DISPLAY_ENVS = sc.DISPLAY_ENVS - {"thebibliography"}

LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
EQREF_RE = re.compile(r"\\eqref\{([^}]*)\}")
ROW_BREAK = re.compile(r"\\\\(?:\[[^\]]*\])?")


def key_of(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:12]


def label_key(label: str) -> str:
    return key_of("\x00label\x00" + label)


def eqref_labels(path: str) -> set[str]:
    """Every label the prose references individually."""
    with open(path, encoding="utf-8") as fh:
        text = "".join(sc.strip_comments(line) for line in fh)
    return set(EQREF_RE.findall(text))


def extract(path: str) -> list[dict]:
    """One record per top-level display block, plus referenced sub-labels."""
    with open(path, encoding="utf-8") as fh:
        raw = fh.readlines()

    referenced = eqref_labels(path)
    records: list[dict] = []

    env_stack: list[str] = []
    section = ""
    anchor = ""
    in_document = False

    # the open top-level display, if any
    open_kind: str | None = None      # environment name, or "\\[" / "$$"
    open_line = 0
    body: list[str] = []

    def close(kind: str) -> None:
        nonlocal open_kind, body
        text = sc.normalize(" ".join(body))
        if re.search(r"[A-Za-z0-9]", text):
            labels = LABEL_RE.findall(" ".join(body))
            records.append({
                "kind": "block",
                "env": kind,
                "line": open_line,
                "section": section,
                "anchor": anchor,
                "label": labels[0] if labels else "",
                "labels": labels,
                "body": text,
            })
            # A line the prose points at individually gets its own row.
            if len(labels) > 1:
                for lab in labels:
                    if lab not in referenced:
                        continue
                    line_text = _line_of_label(body, lab)
                    records.append({
                        "kind": "line",
                        "env": kind,
                        "line": open_line,
                        "section": section,
                        "anchor": anchor,
                        "label": lab,
                        "labels": [lab],
                        "body": sc.normalize(line_text),
                    })
        open_kind = None
        body = []

    def _line_of_label(lines: list[str], lab: str) -> str:
        """The `\\\\`-separated row of the block that carries `lab`."""
        joined = " ".join(lines)
        parts = ROW_BREAK.split(joined)
        for part in parts:
            if f"\\label{{{lab}}}" in part:
                return part
        return joined

    for n, rawline in enumerate(raw, start=1):
        line = sc.strip_comments(rawline).rstrip("\n")
        line = re.sub(r"\\\\\[[^\]]*\]", r"\\\\ ", line)

        if not in_document:
            if r"\begin{document}" in line:
                in_document = True
            continue

        if open_kind is not None:
            # inside a display: look only for its terminator
            if open_kind == "\\[":
                if "\\]" in line:
                    head, _, _ = line.partition("\\]")
                    body.append(head)
                    close("\\[")
                else:
                    body.append(line)
                continue
            if open_kind == "$$":
                if "$$" in line:
                    head, _, _ = line.partition("$$")
                    body.append(head)
                    close("$$")
                else:
                    body.append(line)
                continue
            me = re.match(r"\s*\\end\{([^}]*)\}", line)
            if me and me.group(1) == open_kind:
                close(open_kind)
            else:
                body.append(line)
            continue

        collapsed = sc.collapse_inline_envs(line)

        ms = re.match(r"\s*\\(sub)*section\*?\{(.*?)\}", collapsed)
        if ms:
            section = ms.group(2)
            anchor = ""
            mlab = LABEL_RE.search(collapsed)
            if mlab:
                anchor = mlab.group(1)
            continue

        mb = re.match(r"\s*\\begin\{([^}]*)\}", collapsed)
        me = re.match(r"\s*\\end\{([^}]*)\}", collapsed)

        if mb:
            env = mb.group(1)
            mlab = LABEL_RE.search(collapsed)
            if mlab and env in sc.CLAIM_ENVS:
                anchor = mlab.group(1)
            if env in AUDITED_DISPLAY_ENVS and not any(
                    e in AUDITED_DISPLAY_ENVS for e in env_stack):
                open_kind = env
                open_line = n
                body = [collapsed[mb.end():]]
                continue
            env_stack.append(env)
            continue

        if me:
            if env_stack:
                env_stack.pop()
            continue

        if any(e in AUDITED_DISPLAY_ENVS for e in env_stack):
            continue

        mlab = LABEL_RE.match(collapsed.strip())
        if mlab and (not env_stack or env_stack[-1] in sc.CLAIM_ENVS):
            anchor = LABEL_RE.search(collapsed).group(1)
            continue

        # unnumbered displays
        if "\\[" in collapsed:
            head, _, tail = collapsed.partition("\\[")
            if "\\]" in tail:
                inner, _, _ = tail.partition("\\]")
                open_kind, open_line, body = "\\[", n, [inner]
                close("\\[")
            else:
                open_kind, open_line, body = "\\[", n, [tail]
            continue
        if "$$" in collapsed:
            head, _, tail = collapsed.partition("$$")
            if "$$" in tail:
                inner, _, _ = tail.partition("$$")
                open_kind, open_line, body = "$$", n, [inner]
                close("$$")
            else:
                open_kind, open_line, body = "$$", n, [tail]
            continue

    _assign_keys(records)
    return records


def _assign_keys(records: list[dict]) -> None:
    """Content key for blocks, label key for referenced lines."""
    for r in records:
        if r["kind"] == "line":
            r["key"] = label_key(r["label"])
        else:
            r["key"] = key_of(r["body"])
    by_key: dict[str, list[dict]] = {}
    for r in records:
        by_key.setdefault(r["key"], []).append(r)
    for same in by_key.values():
        if len(same) == 1:
            continue
        seen: dict[str, int] = {}
        for r in same:
            base = r["anchor"] + "\0" + r["body"]
            n = seen.get(base, 0)
            seen[base] = n + 1
            r["key"] = key_of(base if n == 0 else base + f"\0#{n + 1}")
    if len({r["key"] for r in records}) != len(records):
        raise ValueError("display keys are not unique after disambiguation")


def load_map(path: str) -> dict[str, dict]:
    out: dict[str, dict] = {}
    if not os.path.exists(path):
        return out
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            cols = line.split("\t")
            while len(cols) < 4:
                cols.append("")
            if cols[0] in out:
                raise ValueError(f"duplicate display-map key: {cols[0]}")
            out[cols[0]] = {
                "status": cols[1].strip(),
                "decls": cols[2].strip(),
                "note": cols[3].strip(),
            }
    return out


def join(records: list[dict], assignments: dict[str, dict]) -> list[dict]:
    for r in records:
        a = assignments.get(r["key"])
        if a and a.get("status"):
            r.update(a)
            r.setdefault("note", "")
        else:
            r["status"] = "unassigned"
            r["decls"] = ""
            r["note"] = ""
    return records


def overlay_errors(records: list[dict], assignments: dict[str, dict],
                   sentence_keys: set[str],
                   unassigned_sentences: set[str]) -> list[str]:
    errors: list[str] = []
    record_keys = {r["key"] for r in records}
    for key in sorted(set(assignments) - record_keys):
        errors.append(f"stale display-map key {key}")
    for key, a in assignments.items():
        status = a["status"]
        m = DERIVATION.match(status)
        if status in VALID_STATUSES:
            continue
        if not m:
            errors.append(f"{key}: invalid display status {status!r}")
            continue
        if a["decls"]:
            errors.append(
                f"{key}: a derivation-of row must name no declarations; the "
                "grade says the step is not separately stated")
        target = m.group(1)
        if sentence_keys and target not in sentence_keys:
            errors.append(
                f"{key}: derivation-of target {target} is not a sentence key")
        elif target in unassigned_sentences:
            errors.append(
                f"{key}: derivation-of target {target} is itself unassigned")
    return errors


def missing_label_rows(records: list[dict], path: str) -> list[str]:
    """Every `\\eqref`-ed label must have a row."""
    referenced = eqref_labels(path)
    covered: set[str] = set()
    for r in records:
        covered.update(r["labels"])
    return sorted(referenced - covered)


def read_sentence_census(path: str) -> tuple[set[str], set[str]]:
    keys: set[str] = set()
    unassigned: set[str] = set()
    if not os.path.exists(path):
        return keys, unassigned
    with open(path, encoding="utf-8") as fh:
        for i, line in enumerate(fh):
            if i < 2 or line.startswith("#"):
                continue
            cols = line.rstrip("\n").split("\t")
            if len(cols) < 8:
                continue
            keys.add(cols[0])
            if cols[5] == "unassigned":
                unassigned.add(cols[0])
    return keys, unassigned


def verify_decls(records: list[dict]) -> list[str]:
    known = sc.declared_names()
    bad: list[str] = []
    for r in records:
        if r["status"] != "carrier":
            continue
        for d in r["decls"].split():
            if "." not in d:
                continue
            if d.rsplit(".", 1)[1] not in known:
                bad.append(f"{r['key']}\t{d}")
    return bad


def clobber_refusal(tex: str, out: str, out_md: str) -> str | None:
    """Why writing would overwrite another manuscript's census, or `None`.

    Same guard, same reason, as `sentence_census.clobber_refusal`: the outputs
    default to the non-MF paper's files, so a non-default `--tex` with the
    outputs left alone writes one manuscript's census into another's.  This
    script inherits the convention deliberately, so it inherits the refusal.
    """
    if os.path.abspath(tex) == os.path.abspath(DEFAULT_TEX):
        return None
    collisions = [
        flag for flag, value, default in
        (("--out", out, DEFAULT_OUT), ("--out-md", out_md, DEFAULT_OUT_MD))
        if os.path.abspath(value) == os.path.abspath(default)
    ]
    if not collisions:
        return None
    return (
        f"refusing to write: --tex is {os.path.relpath(os.path.abspath(tex), ROOT)} "
        f"but {' and '.join(collisions)} still point at the non-MF paper's "
        "generated files, so this run would overwrite them with another "
        "manuscript's census.  Pass --out/--out-md (a scratch path is fine for "
        "a check), or --summary to print the counts without writing."
    )


def counts(records: list[dict]) -> dict[str, int]:
    out: dict[str, int] = {}
    for r in records:
        status = r["status"]
        if DERIVATION.match(status):
            status = "derivation-of"
        out[status] = out.get(status, 0) + 1
    return out


def write_tsv(records: list[dict], path: str) -> None:
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# GENERATED by scripts/display_census.py -- do not edit.\n")
        fh.write(f"# Edit {MAP_LABEL} and regenerate.\n")
        fh.write("key\tkind\tline\tsection\tenv\tanchor\tlabel\tstatus\t"
                 "decls\tbody\n")
        for r in records:
            fh.write("\t".join([
                r["key"], r["kind"], str(r["line"]), r["section"], r["env"],
                r["anchor"], r["label"], r["status"], r["decls"], r["body"],
            ]) + "\n")


def write_md(records: list[dict], path: str) -> None:
    c = counts(records)
    total = len(records)
    graded = total - c.get("unassigned", 0)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(f"# {TEX_LABEL}: display-level census\n\n")
        fh.write(
            "Generated by `scripts/display_census.py` from "
            f"`{TEX_LABEL}`.  Do not edit: the assignments live in "
            f"`{MAP_LABEL}` and everything here is their join with the "
            "extraction.\n\n")
        fh.write(
            "`sentence_census.py` deletes display material before splitting "
            "prose into sentences.  This census grades what it deletes: one "
            "row per top-level display block, plus a row for any line the "
            "prose `\\eqref`s individually.\n\n")
        fh.write("| status | displays |\n| --- | --- |\n")
        for k in sorted(c, key=lambda k: -c[k]):
            fh.write(f"| `{k}` | {c[k]} |\n")
        fh.write(f"| **total** | **{total}** |\n\n")
        fh.write(f"Graded: **{graded}/{total}** "
                 f"({100.0 * graded / max(total, 1):.1f}%).\n\n")
        gaps = [r for r in records if r["status"] == "unassigned"]
        fh.write("## Ungraded displays\n\n")
        if not gaps:
            fh.write("Every display carries a grade.\n\n")
        else:
            for r in gaps:
                where = r["label"] or r["anchor"] or r["section"] or "(none)"
                fh.write(f"* line {r['line']}, `{r['env']}`, at {where} --- "
                         f"`{r['body'][:160]}`\n")
            fh.write("\n")


def self_test() -> int:
    """Pin the refusal, the same way `sentence_census.py --self-test` does."""
    other = os.path.join(ROOT, "mf_recognition_complexity.tex")
    cases = [
        (DEFAULT_TEX, DEFAULT_OUT, DEFAULT_OUT_MD, False),
        (DEFAULT_TEX, "/tmp/a.tsv", "/tmp/a.md", False),
        (other, "/tmp/a.tsv", "/tmp/a.md", False),
        (other, DEFAULT_OUT, DEFAULT_OUT_MD, True),
        (other, DEFAULT_OUT, "/tmp/a.md", True),
        (other, "/tmp/a.tsv", DEFAULT_OUT_MD, True),
    ]
    for tex, out, out_md, must_refuse in cases:
        refusal = clobber_refusal(tex, out, out_md)
        if bool(refusal) != must_refuse:
            print(f"self-test: clobber_refusal({os.path.basename(tex)}, "
                  f"{os.path.basename(out)}, {os.path.basename(out_md)}) "
                  f"= {refusal!r}, expected refuse={must_refuse}",
                  file=sys.stderr)
            return 1
    print("display-census: self-test passed")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tex", default=DEFAULT_TEX)
    ap.add_argument("--map", dest="map_path", default=DEFAULT_MAP)
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--out-md", default=DEFAULT_OUT_MD)
    ap.add_argument("--sentence-census", default=DEFAULT_SENTENCE_CENSUS)
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--self-test", action="store_true",
                    help="pin the refusal that keeps one manuscript's census "
                         "out of another's file")
    ap.add_argument("--check", action="store_true",
                    help="exit nonzero if any display is unassigned")
    ap.add_argument("--verify-decls", action="store_true")
    ap.add_argument("--verify-links", action="store_true",
                    help="derivation targets resolve, and every \\eqref-ed "
                         "label has a row")
    args = ap.parse_args()
    if args.self_test:
        return self_test()

    global TEX_LABEL, MAP_LABEL
    TEX_LABEL = os.path.relpath(os.path.abspath(args.tex), ROOT)
    MAP_LABEL = os.path.relpath(os.path.abspath(args.map_path), ROOT)

    records = extract(args.tex)
    assignments = load_map(args.map_path)
    sentence_keys, unassigned_sentences = read_sentence_census(
        args.sentence_census)
    records = join(records, assignments)
    errors = overlay_errors(records, assignments, sentence_keys,
                            unassigned_sentences)

    if args.verify_decls:
        bad = verify_decls(records)
        for b in bad:
            print("MISSING DECL\t" + b)
        print(f"{len(bad)} missing of "
              f"{sum(len(r['decls'].split()) for r in records)} named")
        return 1 if bad else 0

    if args.verify_links:
        missing = missing_label_rows(records, args.tex)
        for lab in missing:
            print(f"UNCOVERED LABEL\t{lab}")
        for e in errors:
            print(f"OVERLAY ERROR: {e}")
        print(f"{len(missing)} referenced label(s) without a row, "
              f"{len(errors)} overlay error(s)")
        return 1 if (missing or errors) else 0

    if not args.summary:
        refusal = clobber_refusal(args.tex, args.out, args.out_md)
        if refusal:
            print(refusal, file=sys.stderr)
            return 2
        write_tsv(records, args.out)
        write_md(records, args.out_md)

    c = counts(records)
    for k in sorted(c, key=lambda k: -c[k]):
        print(f"{k:16s} {c[k]:5d}")
    print(f"{'total':16s} {len(records):5d}")
    for e in errors:
        print(f"OVERLAY ERROR: {e}")

    if args.check and (c.get("unassigned") or errors):
        if c.get("unassigned"):
            print(f"\nFAIL: {c['unassigned']} displays carry no grade.")
        if errors:
            print(f"FAIL: {len(errors)} overlay integrity error(s).")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
