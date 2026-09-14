#!/usr/bin/env python3
r"""Sentence-level census of simple_kazhdan_sofic_group.tex.

This is the companion-manuscript form of `scripts/sentence_census.py`.  It
imports that module, unmodified, and reuses its normalization, keying,
anchoring and join, so a sentence of the note is keyed the way a sentence of
the non-MF paper is.  It changes three things.

1. **Word-boundary abbreviations.**  The non-MF splitter protects an
   abbreviation by plain substring replacement, so "killed." (ending in "ed.")
   and "trivial." (ending in "al.") never ended a sentence, and two sentences
   shared one row.  Here an abbreviation is protected only when no letter
   precedes it.
2. **Displays are rows.**  The non-MF splitter drops unnumbered displays, so a
   lead-in fragment such as "Put" was the only row carrying the displayed
   mathematics.  Here every display is its own record: `\[...\]`, `$$...$$` and
   each math display environment, numbered or not.  Its env is `display` or the
   environment's name, and its sentence text is `[display] <normalized body>`.
3. **Sentence spans.**  Each record knows the lines on which it starts and
   ends, so a lane can key a row `LINE:<n>@<commit>` by any line the sentence
   occupies.

    scripts/sk_sentence_census.py --tex-commit <sha>           regenerate
    scripts/sk_sentence_census.py --tex-commit <sha> --merge   fold row files in first
    scripts/sk_sentence_census.py --summary                    counts only

`metadata/SK_SENTENCE_MAP.tsv` is the overlay, `key<TAB>status<TAB>decls<TAB>note`.
`--merge` folds `metadata/sk-census-rows/*.tsv` into it.  A row keyed by a
12-hex key applies directly.  A row keyed `LINE:<n>@<commit>` applies only when
the commit prefix matches `--tex-commit` and the line meets exactly one record
(or starts exactly one; an environment line resolves to the record starting on
the next line).  Anything else is reported and left out, never guessed.
"""

from __future__ import annotations

import argparse
import bisect
import glob
import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import sentence_census as sc  # noqa: E402

TEX = os.path.join(ROOT, "simple_kazhdan_sofic_group.tex")
MAP = os.path.join(ROOT, "metadata", "SK_SENTENCE_MAP.tsv")
OUT = os.path.join(ROOT, "metadata", "SK_SENTENCE_CENSUS.tsv")
OUT_MD = os.path.join(ROOT, "metadata", "SK_SENTENCE_CENSUS.md")
ROWS_DIR = os.path.join(ROOT, "metadata", "sk-census-rows")

MATH_DISPLAY_ENVS = {
    "equation", "equation*", "align", "align*", "gather", "gather*",
    "multline", "multline*", "displaymath", "eqnarray", "eqnarray*",
    "flalign", "flalign*", "alignat", "alignat*",
}
VALID_STATUSES = {
    "formalized", "partial", "definition", "structural", "attribution",
    "provenance", "open",
}
LINE_KEY = re.compile(r"^LINE:(\d+)(?:@([0-9a-f]{7,40}))?$")
DISPLAY_RE = re.compile(r"\\\[(.*?)\\\]|\$\$(.*?)\$\$", re.S)
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")


def protect(text: str) -> str:
    """`sc.protect` with abbreviations matched at a word boundary.

    Every substitution replaces a period by one byte, so offsets survive.
    """
    text = re.sub(r"\$[^$]*\$", lambda m: m.group(0).replace(".", "\x00"), text)
    text = re.sub(r"\\[a-zA-Z]+\s*\{[^{}]*\}",
                  lambda m: m.group(0).replace(".", "\x00"), text)
    for a in sc.ABBREV:
        text = re.sub(r"(?<![A-Za-z])" + re.escape(a) + r"\.",
                      lambda m: m.group(0)[:-1] + "\x00", text)
    return re.sub(r"(?<=\d)\.(?=\d)", "\x00", text)


def split_with_offsets(text: str) -> list[tuple[int, str]]:
    """Sentences of `text` with their start offsets."""
    guarded = protect(text)
    out: list[tuple[int, str]] = []
    pos = 0
    bounds = [(m.start(), m.end()) for m in sc.SENTENCE_END.finditer(guarded)]
    for start, end in bounds + [(len(guarded), len(guarded))]:
        seg = guarded[pos:start]
        if seg.strip():
            lead = len(seg) - len(seg.lstrip())
            out.append((pos + lead, sc.unprotect(seg.strip())))
        pos = end
    return out


def collapse_inline_envs(line: str) -> str:
    r"""`sc.collapse_inline_envs`, keeping a one-line math display as `\[...\]`."""
    def repl(m: re.Match) -> str:
        env, body = m.group(1), m.group(2)
        if env in MATH_DISPLAY_ENVS:
            return " \\[" + body + "\\] "
        return " " if env in sc.DISPLAY_ENVS else body

    while True:
        collapsed = sc.INLINE_ENV_RE.sub(repl, line)
        if collapsed == line:
            return line
        line = collapsed


def extract(path: str) -> list[dict]:
    """Walk the tex and return one record per sentence and per display."""
    with open(path, encoding="utf-8") as fh:
        raw = fh.readlines()

    records: list[dict] = []
    env_stack: list[str] = []
    section = ""
    label = ""
    in_document = False
    para: list[tuple[int, str]] = []

    def add(line_no: int, end_no: int, env: str, lab: str, clean: str,
            badges: list[str], steps: list[str]) -> None:
        records.append({"key": sc.key_of(clean), "line": line_no,
                        "end": max(line_no, end_no), "section": section,
                        "env": env, "label": lab, "badges": badges,
                        "steps": steps, "sentence": clean})

    def add_display(line_no: int, end_no: int, env: str, body: str) -> None:
        mlab = LABEL_RE.search(body)
        body = sc.normalize(LABEL_RE.sub(" ", body))
        if body:
            add(line_no, end_no, env, mlab.group(1) if mlab else label,
                "[display] " + body, [], [])

    def flush() -> None:
        nonlocal para
        if not para:
            return
        pieces, para = para, []
        text = " ".join(t for _, t in pieces)
        starts: list[int] = []
        pos = 0
        for _, t in pieces:
            starts.append(pos)
            pos += len(t) + 1

        def line_at(offset: int) -> int:
            return pieces[max(0, bisect.bisect_right(starts, offset) - 1)][0]

        env = env_stack[-1] if env_stack else ""
        chunks: list[tuple[str, int, int, str]] = []
        cursor = 0
        for m in DISPLAY_RE.finditer(text):
            chunks.append(("prose", cursor, m.start(), text[cursor:m.start()]))
            body = m.group(1) if m.group(1) is not None else m.group(2)
            chunks.append(("display", m.start(), m.end(), body))
            cursor = m.end()
        chunks.append(("prose", cursor, len(text), text[cursor:]))
        for kind, offset, stop, chunk in chunks:
            if kind == "display":
                add_display(line_at(offset), line_at(max(offset, stop - 1)),
                            "display", chunk)
                continue
            for rel, s in split_with_offsets(chunk):
                badges = [d for _, d in sc.BADGE_VERIFIED.findall(s)]
                steps = sc.BADGE_STEP.findall(s)
                clean = sc.normalize(sc.BADGE_STEP.sub("", sc.BADGE_ANY.sub("", s)))
                if re.search(r"[A-Za-z]", clean):
                    add(line_at(offset + rel), line_at(offset + rel + max(0, len(s) - 1)),
                        env, label, clean, badges, steps)

    in_display = False
    disp_start, disp_lines = 0, []
    cap: dict | None = None
    front_depth = 0

    for n, rawline in enumerate(raw, start=1):
        line = re.sub(r"\\\\\[[^\]]*\]", " ", sc.strip_comments(rawline).rstrip("\n"))

        if cap is not None:
            end = "\\end{" + cap["env"] + "}"
            if end not in line:
                cap["lines"].append(line)
                continue
            before, line = line.split(end, 1)
            cap["lines"].append(before)
            add_display(cap["start"], n, cap["env"], " ".join(cap["lines"]))
            cap = None
            if not line.strip():
                continue

        line = collapse_inline_envs(line)

        if in_display:
            if "\\]" not in line:
                disp_lines.append(line)
                continue
            before, line = line.split("\\]", 1)
            disp_lines.append(before)
            flush()
            add_display(disp_start, n, "display", " ".join(disp_lines))
            in_display = False
        if "\\[" in line and "\\]" not in line.split("\\[", 1)[1]:
            line, rest = line.split("\\[", 1)
            disp_start, disp_lines, in_display = n, [rest], True

        if front_depth:
            front_depth = max(0, front_depth + line.count("{") - line.count("}"))
            continue

        if re.match(r"^\s*\\label\{[^}]*\}\s*$", line):
            mlab = LABEL_RE.search(line)
            if mlab and (not env_stack or env_stack[-1] in sc.CLAIM_ENVS):
                label = mlab.group(1)
            continue

        if not in_document:
            in_document = r"\begin{document}" in line
            continue

        if sc.FRONT_MATTER.match(line) or sc.LAYOUT_ONLY.match(line):
            flush()
            front_depth = max(0, line.count("{") - line.count("}"))
            continue

        mb = re.match(r"\s*\\begin\{([^}]*)\}", line)
        me = re.match(r"\s*\\end\{([^}]*)\}", line)
        ms = re.match(r"\s*\\(sub)*section\*?\{(.*?)\}", line)

        if ms:
            flush()
            section = ms.group(2)
            mlab = LABEL_RE.search(line)
            label = mlab.group(1) if mlab else ""
            continue

        if mb:
            flush()
            env = mb.group(1)
            rest = re.sub(r"^\[[^\]]*\]", "", line[mb.end():])
            if env in MATH_DISPLAY_ENVS:
                cap = {"start": n, "env": env, "lines": [rest]}
                continue
            env_stack.append(env)
            mlab = LABEL_RE.search(line)
            if mlab and env in sc.CLAIM_ENVS:
                label = mlab.group(1)
            if env in sc.DISPLAY_ENVS:
                continue
            rest = LABEL_RE.sub("", rest)
            if rest.strip():
                para.append((n, rest.strip()))
            continue

        if me:
            flush()
            if env_stack:
                env_stack.pop()
            continue

        if env_stack and env_stack[-1] in sc.DISPLAY_ENVS:
            continue

        if not line.strip():
            flush()
            continue

        mlab = LABEL_RE.search(line)
        if mlab and (not env_stack or env_stack[-1] in sc.CLAIM_ENVS):
            label = mlab.group(1)

        if re.match(r"\s*\\item\b", line):
            flush()
            line = re.sub(r"^\s*\\item\s*", "", line)

        para.append((n, line.strip()))

    flush()
    return records


def load_rows(rows_dir: str, records: list[dict], overlay: dict[str, dict],
              tex_commit: str, tex_lines: list[str]) -> tuple[dict[str, dict], list[str]]:
    """Fold the lanes' row files into the overlay; report what cannot apply."""
    spans = [(r["line"], r.get("end", r["line"]), r["key"]) for r in records]
    known = {r["key"] for r in records}

    def resolve(ln: int) -> tuple[str | None, str]:
        containing = [k for s, e, k in spans if s <= ln <= e]
        starting = [k for s, e, k in spans if s == ln]
        if len(containing) == 1:
            return containing[0], ""
        if len(starting) == 1:
            return starting[0], ""
        if not containing:
            text = tex_lines[ln - 1] if 0 < ln <= len(tex_lines) else ""
            nxt = [k for s, e, k in spans if s == ln + 1]
            if re.match(r"\s*\\begin\{", text) and len(nxt) == 1:
                return nxt[0], ""
            return None, (f"line {ln} carries no census row (a heading, an environment "
                          "line, the bibliography or a blank line)")
        return None, (f"line {ln} meets {len(containing)} rows ({' '.join(containing)}); "
                      "key the row by one of them")

    merged = {k: dict(v) for k, v in overlay.items()}
    owner = {k: "map" for k in overlay}
    errors: list[str] = []
    for path in sorted(glob.glob(os.path.join(rows_dir, "*.tsv"))):
        lane = os.path.splitext(os.path.basename(path))[0]
        with open(path, encoding="utf-8") as fh:
            for n, raw_row in enumerate(fh, start=1):
                row = raw_row.rstrip("\n")
                if not row.strip() or row.startswith("#"):
                    continue
                cols = (row.split("\t", 3) + ["", "", ""])[:4]
                key, status = cols[0].strip(), cols[1].strip()
                where = f"rows/{lane}.tsv:{n}"
                m = LINE_KEY.match(key)
                if m:
                    commit = m.group(2) or ""
                    if not commit or not tex_commit.startswith(commit):
                        errors.append(f"{where}: {key} is not keyed at manuscript "
                                      f"commit {tex_commit[:9]}")
                        continue
                    hit, why = resolve(int(m.group(1)))
                    if hit is None:
                        errors.append(f"{where}: {key}: {why}")
                        continue
                    key = hit
                elif key not in known:
                    errors.append(f"{where}: unknown sentence key {key!r}")
                    continue
                if status not in VALID_STATUSES:
                    errors.append(f"{where}: invalid status {status!r}")
                    continue
                prev = owner.get(key)
                if prev not in (None, "map", lane) and merged[key]["status"] != status:
                    errors.append(f"{where}: {key} conflicts with rows/{prev}.tsv "
                                  f"({merged[key]['status']} vs {status}); kept rows/{prev}.tsv")
                    continue
                note = cols[3].replace("\t", " ").strip()
                merged[key] = {"status": status, "decls": cols[2].strip(),
                               "note": f"{note} [rows/{lane}]".strip()}
                owner[key] = lane
    return merged, errors


def write_map(path: str, records: list[dict], merged: dict[str, dict]) -> None:
    order = {r["key"]: (r["line"], i) for i, r in enumerate(records)}
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# Sentence assignments for simple_kazhdan_sofic_group.tex.\n")
        fh.write("# key<TAB>status<TAB>decls<TAB>note\n")
        fh.write("# Merged from metadata/sk-census-rows/*.tsv by scripts/sk_sentence_census.py --merge.\n")
        for key in sorted(merged, key=lambda k: order.get(k, (10 ** 9, 0))):
            e = merged[key]
            fh.write("\t".join([key, e["status"], e["decls"], e["note"]]) + "\n")


def write_tsv(records: list[dict], path: str, sha256: str, commit: str) -> None:
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# GENERATED by scripts/sk_sentence_census.py -- do not edit.\n")
        fh.write("# Land rows under metadata/sk-census-rows/ and regenerate with --merge.\n")
        fh.write(f"# Manuscript simple_kazhdan_sofic_group.tex at commit {commit}, SHA-256 {sha256}\n")
        fh.write("key\tline\tend\tsection\tenv\tlabel\tstatus\tdecls\tsentence\n")
        for r in records:
            fh.write("\t".join([r["key"], str(r["line"]), str(r.get("end", r["line"])),
                                r["section"], r["env"], r["label"], r["status"],
                                r["decls"], r["sentence"]]) + "\n")


def write_md(records: list[dict], path: str, sha256: str, commit: str,
             merge_errors: list[str]) -> None:
    c = sc.counts(records)
    total = len(records)
    done = c.get("formalized", 0) + c.get("definition", 0)
    displays = sum(1 for r in records if r["sentence"].startswith("[display] "))
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# simple_kazhdan_sofic_group.tex: sentence-level census\n\n")
        fh.write("Generated by `scripts/sk_sentence_census.py`.  Do not edit: the "
                 "assignments live in `metadata/SK_SENTENCE_MAP.tsv`, merged from "
                 "`metadata/sk-census-rows/`.\n\n")
        fh.write(f"Manuscript commit `{commit}`, SHA-256 `{sha256}`.\n\n")
        fh.write(f"Rows: {total} ({total - displays} prose sentences, {displays} "
                 "displays).  Assignments do not attest to a successful Lean build.\n\n")
        fh.write("| status | rows |\n| --- | --- |\n")
        for k in sorted(c, key=lambda k: -c[k]):
            fh.write(f"| `{k}` | {c[k]} |\n")
        fh.write(f"| **total** | **{total}** |\n\n")
        fh.write(f"Completely formalized or definitional: **{done}/{total}** "
                 f"({100.0 * done / max(total, 1):.1f}%).\n\n")
        if merge_errors:
            fh.write("## Rows not merged\n\n")
            for e in merge_errors:
                fh.write(f"* {e}\n")
            fh.write("\n")
        fh.write("## Rows without complete recorded coverage\n\n")
        for r in records:
            if r["status"] in {"partial", "open", "unassigned"}:
                fh.write(f"* **`{r['status']}`** `{r['key']}`, lines {r['line']}"
                         f"--{r.get('end', r['line'])} --- {r['sentence'][:240]}\n")
                if r.get("note"):
                    fh.write(f"  * {r['note']}\n")
        fh.write("\n## By section\n\n| section | rows | unassigned |\n| --- | --- | --- |\n")
        secs: dict[str, list[int]] = {}
        for r in records:
            s = secs.setdefault(r["section"] or "(front matter)", [0, 0])
            s[0] += 1
            s[1] += int(r["status"] == "unassigned")
        for k, v in secs.items():
            fh.write(f"| {k} | {v[0]} | {v[1]} |\n")


def main() -> int:
    ap = argparse.ArgumentParser(description="sentence census of the simple Kazhdan note")
    ap.add_argument("--tex", default=TEX)
    ap.add_argument("--map", dest="map_path", default=MAP)
    ap.add_argument("--rows-dir", default=ROWS_DIR)
    ap.add_argument("--out", default=OUT)
    ap.add_argument("--out-md", default=OUT_MD)
    ap.add_argument("--tex-commit", default="",
                    help="commit of --tex; LINE:<n>@<commit> rows must match it")
    ap.add_argument("--merge", action="store_true")
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--list-unassigned", action="store_true")
    args = ap.parse_args()

    protected = {os.path.abspath(p) for p in (sc.OUT, sc.OUT_MD, sc.MAP)}
    for flag, value in (("--out", args.out), ("--out-md", args.out_md),
                        ("--map", args.map_path)):
        if os.path.abspath(value) in protected:
            print(f"refusing to write: {flag} points at the non-MF paper's census files",
                  file=sys.stderr)
            return 2
    if args.merge and not args.tex_commit:
        print("--merge needs --tex-commit, so LINE@<commit> rows can be checked",
              file=sys.stderr)
        return 2

    with open(args.tex, "rb") as fh:
        source = fh.read()
    sha256 = hashlib.sha256(source).hexdigest()
    tex_lines = source.decode("utf-8").splitlines()
    commit = args.tex_commit or "(unrecorded)"
    records = extract(args.tex)
    sc.attach_anchors(records, args.tex, [])
    overlay = sc.load_map(args.map_path)
    merge_errors: list[str] = []
    if args.merge:
        overlay, merge_errors = load_rows(args.rows_dir, records, overlay,
                                          args.tex_commit, tex_lines)
        if not args.summary:
            write_map(args.map_path, records, overlay)
    records = sc.join(records, overlay, {}, badges_need_rows=True)

    known = {r["key"] for r in records}
    overlay_errors = [f"stale overlay key {k}" for k in sorted(set(overlay) - known)]
    overlay_errors += [f"{k}: invalid overlay status {v['status']!r}"
                       for k, v in overlay.items() if v["status"] not in VALID_STATUSES]

    if args.list_unassigned:
        for r in records:
            if r["status"] == "unassigned":
                print(f"{r['key']}\t{r['line']}\t{r['label'] or r['env'] or r['section']}"
                      f"\t{r['sentence'][:160]}")
        return 0

    if not args.summary:
        write_tsv(records, args.out, sha256, commit)
        write_md(records, args.out_md, sha256, commit, merge_errors)

    c = sc.counts(records)
    for k in sorted(c, key=lambda k: -c[k]):
        print(f"{k:14s} {c[k]:5d}")
    print(f"{'total':14s} {len(records):5d}")
    for e in merge_errors:
        print("MERGE ERROR: " + e)
    for e in overlay_errors:
        print("OVERLAY ERROR: " + e)
    if args.check and (c.get("unassigned") or overlay_errors):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
