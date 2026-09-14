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
   ends.

    scripts/sk_sentence_census.py --tex-commit <sha> --merge \
        [--prev-census <old census tsv> --prev-tex <old tex>]
    scripts/sk_sentence_census.py --summary

Rows live in `metadata/sk-census-rows/<lane>.tsv` as
`key<TAB>status<TAB>decls<TAB>note`.  The key should be a 12-hex sentence hash
from `metadata/SK_SENTENCE_CENSUS.tsv`: hashes survive line moves and edits
elsewhere in the paragraph.  `LINE:<n>@<commit>` is accepted at the current
commit, and at the previous census's commit when `--prev-census` is given.

`--merge` derives `metadata/SK_SENTENCE_MAP.tsv` from the row files alone, so
the map is a function of the rows and the manuscript.  A row whose sentence
still exists at the tip (same hash) is applied.  A row whose sentence was
reworded or removed is **superseded**: it is listed in
`metadata/SK_SENTENCE_SUPERSEDED.tsv` with its old text and the closest new
sentence as a hint, and it is never applied by guess.
"""

from __future__ import annotations

import argparse
import bisect
import difflib
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
SUPERSEDED = os.path.join(ROOT, "metadata", "SK_SENTENCE_SUPERSEDED.tsv")
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
HEX_KEY = re.compile(r"^[0-9a-f]{12}$")
COMMIT_IN_HEADER = re.compile(r"at commit ([0-9a-f]{7,40})")
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


class Resolver:
    """Resolve `LINE:<n>` against one manuscript version's record spans."""

    def __init__(self, spans: list[tuple[int, int, str]], tex_lines: list[str]):
        self.spans = spans
        self.tex_lines = tex_lines

    def __call__(self, ln: int) -> tuple[str | None, str]:
        containing = [k for s, e, k in self.spans if s <= ln <= e]
        starting = [k for s, e, k in self.spans if s == ln]
        if len(containing) == 1:
            return containing[0], ""
        if len(starting) == 1:
            return starting[0], ""
        if not containing:
            text = self.tex_lines[ln - 1] if 0 < ln <= len(self.tex_lines) else ""
            nxt = [k for s, e, k in self.spans if s == ln + 1]
            if re.match(r"\s*\\begin\{", text) and len(nxt) == 1:
                return nxt[0], ""
            return None, (f"line {ln} carries no census row (a heading, an environment "
                          "line, the bibliography or a blank line)")
        return None, (f"line {ln} meets {len(containing)} rows ({' '.join(containing)}); "
                      "key the row by one of them")


def load_prev(census_path: str, tex_path: str) -> dict:
    """The previous census: its commit, key -> (line, end, sentence), a resolver."""
    commit, rows = "", {}
    with open(census_path, encoding="utf-8") as fh:
        for raw_row in fh:
            row = raw_row.rstrip("\n")
            if row.startswith("#"):
                m = COMMIT_IN_HEADER.search(row)
                commit = m.group(1) if m else commit
                continue
            cols = row.split("\t")
            if len(cols) < 9 or cols[0] == "key":
                continue
            rows[cols[0]] = (int(cols[1]), int(cols[2]), cols[8])
    tex_lines: list[str] = []
    if tex_path and os.path.exists(tex_path):
        with open(tex_path, encoding="utf-8") as fh:
            tex_lines = fh.read().splitlines()
    spans = [(s, e, k) for k, (s, e, _t) in rows.items()]
    return {"commit": commit, "rows": rows, "resolve": Resolver(spans, tex_lines)}


def nearest(sentence: str, records: list[dict]) -> tuple[str, float]:
    best, score = "", 0.0
    for r in records:
        ratio = difflib.SequenceMatcher(None, sentence, r["sentence"]).ratio()
        if ratio > score:
            best, score = r["key"], ratio
    return best, score


def load_rows(rows_dir: str, records: list[dict], tex_commit: str,
              tex_lines: list[str], prev: dict | None
              ) -> tuple[dict[str, dict], list[str], list[dict]]:
    """Derive the overlay from the lanes' row files.

    Returns the overlay, the merge errors, and the superseded rows.
    """
    resolve_now = Resolver([(r["line"], r["end"], r["key"]) for r in records], tex_lines)
    known = {r["key"] for r in records}
    merged: dict[str, dict] = {}
    owner: dict[str, str] = {}
    errors: list[str] = []
    superseded: list[dict] = []

    def supersede(lane: str, where: str, old_key: str, status: str, decls: str,
                  note: str) -> None:
        line, end, text = prev["rows"].get(old_key, (0, 0, ""))
        hint, score = nearest(text, records) if text else ("", 0.0)
        superseded.append({"where": where, "lane": lane, "old_key": old_key,
                           "old_commit": prev["commit"], "old_lines": f"{line}-{end}",
                           "status": status, "decls": decls, "note": note,
                           "old_sentence": text,
                           "hint": hint if score >= 0.6 else "",
                           "similarity": f"{score:.2f}" if score >= 0.6 else ""})

    for path in sorted(glob.glob(os.path.join(rows_dir, "*.tsv"))):
        lane = os.path.splitext(os.path.basename(path))[0]
        with open(path, encoding="utf-8") as fh:
            for n, raw_row in enumerate(fh, start=1):
                row = raw_row.rstrip("\n")
                if not row.strip() or row.startswith("#"):
                    continue
                cols = (row.split("\t", 3) + ["", "", ""])[:4]
                key, status = cols[0].strip(), cols[1].strip()
                decls, note = cols[2].strip(), cols[3].replace("\t", " ").strip()
                where = f"rows/{lane}.tsv:{n}"
                if status not in VALID_STATUSES:
                    errors.append(f"{where}: invalid status {status!r}")
                    continue
                carried = ""
                m = LINE_KEY.match(key)
                if m:
                    commit = m.group(2) or ""
                    if commit and tex_commit.startswith(commit):
                        hit, why = resolve_now(int(m.group(1)))
                    elif commit and prev and prev["commit"].startswith(commit):
                        hit, why = prev["resolve"](int(m.group(1)))
                        carried = prev["commit"][:9]
                    else:
                        errors.append(f"{where}: {key} is keyed at no known manuscript "
                                      f"commit (current {tex_commit[:9]}"
                                      + (f", previous {prev['commit'][:9]}" if prev else "")
                                      + ")")
                        continue
                    if hit is None:
                        errors.append(f"{where}: {key}: {why}")
                        continue
                    key = hit
                elif not HEX_KEY.match(key):
                    errors.append(f"{where}: malformed key {key!r}")
                    continue
                if key not in known:
                    if prev and key in prev["rows"]:
                        supersede(lane, where, key, status, decls, note)
                    else:
                        errors.append(f"{where}: unknown sentence key {key!r}")
                    continue
                prior = owner.get(key)
                if prior not in (None, lane) and merged[key]["status"] != status:
                    errors.append(f"{where}: {key} conflicts with rows/{prior}.tsv "
                                  f"({merged[key]['status']} vs {status}); kept rows/{prior}.tsv")
                    continue
                tag = f"[rows/{lane}" + (f", carried from @{carried}" if carried else "") + "]"
                merged[key] = {"status": status, "decls": decls,
                               "note": f"{note} {tag}".strip()}
                owner[key] = lane
    return merged, errors, superseded


def write_map(path: str, records: list[dict], merged: dict[str, dict]) -> None:
    order = {r["key"]: (r["line"], i) for i, r in enumerate(records)}
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# Sentence assignments for simple_kazhdan_sofic_group.tex.\n")
        fh.write("# key<TAB>status<TAB>decls<TAB>note\n")
        fh.write("# Derived from metadata/sk-census-rows/*.tsv by scripts/sk_sentence_census.py --merge; do not edit.\n")
        for key in sorted(merged, key=lambda k: order.get(k, (10 ** 9, 0))):
            e = merged[key]
            fh.write("\t".join([key, e["status"], e["decls"], e["note"]]) + "\n")


def write_superseded(path: str, entries: list[dict], commit: str) -> None:
    cols = ["where", "lane", "old_key", "old_commit", "old_lines", "status", "decls",
            "note", "old_sentence", "hint", "similarity"]
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# GENERATED by scripts/sk_sentence_census.py --merge -- do not edit.\n")
        fh.write(f"# Rows whose sentence does not survive at commit {commit}.  They are not applied.\n")
        fh.write("# Re-key each row by the current hash after checking the carrier against the new text;\n")
        fh.write("# `hint` is the most similar current sentence (similarity >= 0.60), never applied.\n")
        fh.write("\t".join(cols) + "\n")
        for e in entries:
            fh.write("\t".join(str(e[c]).replace("\t", " ") for c in cols) + "\n")


def header_lines(sha256: str, md5: str, commit: str) -> str:
    return (f"# Manuscript simple_kazhdan_sofic_group.tex at commit {commit}, "
            f"SHA-256 {sha256}, md5 {md5}\n")


def write_tsv(records: list[dict], path: str, sha256: str, md5: str, commit: str) -> None:
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# GENERATED by scripts/sk_sentence_census.py -- do not edit.\n")
        fh.write("# Land rows under metadata/sk-census-rows/ and regenerate with --merge.\n")
        fh.write(header_lines(sha256, md5, commit))
        fh.write("key\tline\tend\tsection\tenv\tlabel\tstatus\tdecls\tsentence\n")
        for r in records:
            fh.write("\t".join([r["key"], str(r["line"]), str(r["end"]),
                                r["section"], r["env"], r["label"], r["status"],
                                r["decls"], r["sentence"]]) + "\n")


def md_cell(text: str, limit: int) -> str:
    text = text if len(text) <= limit else text[: limit - 1] + "…"
    return text.replace("|", "\\|")


def key_table(records: list[dict]) -> str:
    out: list[str] = []
    current = None
    for r in records:
        sec = r["section"] or "(abstract and introduction)"
        if sec != current:
            current = sec
            out.append(f"\n### {sec}\n\n| key | lines | status | sentence |\n| --- | --- | --- | --- |")
        out.append(f"| `{r['key']}` | {r['line']}–{r['end']} | {r['status']} | "
                   f"{md_cell(r['sentence'], 110)} |")
    return "\n".join(out) + "\n"


def write_md(records: list[dict], path: str, sha256: str, md5: str, commit: str,
             merge_errors: list[str], superseded: list[dict]) -> None:
    c = sc.counts(records)
    total = len(records)
    done = c.get("formalized", 0) + c.get("definition", 0)
    displays = sum(1 for r in records if r["sentence"].startswith("[display] "))
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# simple_kazhdan_sofic_group.tex: sentence-level census\n\n")
        fh.write("Generated by `scripts/sk_sentence_census.py`.  Do not edit: the "
                 "assignments live in `metadata/sk-census-rows/`, and the derived "
                 "overlay is `metadata/SK_SENTENCE_MAP.tsv`.\n\n")
        fh.write(f"Manuscript commit `{commit}`, SHA-256 `{sha256}`, md5 `{md5}`.\n\n")
        fh.write(f"Rows: {total} ({total - displays} prose sentences, {displays} "
                 "displays).  Assignments do not attest to a successful Lean build.\n\n")
        fh.write("| status | rows |\n| --- | --- |\n")
        for k in sorted(c, key=lambda k: -c[k]):
            fh.write(f"| `{k}` | {c[k]} |\n")
        fh.write(f"| **total** | **{total}** |\n\n")
        fh.write(f"Completely formalized or definitional: **{done}/{total}** "
                 f"({100.0 * done / max(total, 1):.1f}%).\n\n")
        if superseded:
            fh.write("## Superseded rows (sentence reworded or removed)\n\n")
            for e in superseded:
                hint = (f"; closest now `{e['hint']}` ({e['similarity']})" if e["hint"] else "")
                fh.write(f"* {e['where']} `{e['old_key']}` ({e['status']}, old lines "
                         f"{e['old_lines']} @{e['old_commit'][:9]}){hint} --- "
                         f"{md_cell(e['old_sentence'], 200)}\n")
            fh.write("\n")
        if merge_errors:
            fh.write("## Rows not merged\n\n")
            for e in merge_errors:
                fh.write(f"* {e}\n")
            fh.write("\n")
        fh.write("## Keys by section\n")
        fh.write(key_table(records))
        fh.write("\n## By section\n\n| section | rows | unassigned |\n| --- | --- | --- |\n")
        secs: dict[str, list[int]] = {}
        for r in records:
            s = secs.setdefault(r["section"] or "(abstract and introduction)", [0, 0])
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
    ap.add_argument("--superseded", default=SUPERSEDED)
    ap.add_argument("--key-table", default="",
                    help="also write the section -> key table to this markdown file")
    ap.add_argument("--tex-commit", default="",
                    help="commit of --tex; LINE:<n>@<commit> rows must match it")
    ap.add_argument("--prev-census", default="",
                    help="the previous generated census tsv, to carry rows across a manuscript edit")
    ap.add_argument("--prev-tex", default="", help="the manuscript at the previous census's commit")
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
    md5 = hashlib.md5(source).hexdigest()
    tex_lines = source.decode("utf-8").splitlines()
    commit = args.tex_commit or "(unrecorded)"
    records = extract(args.tex)
    sc.attach_anchors(records, args.tex, [])
    prev = load_prev(args.prev_census, args.prev_tex) if args.prev_census else None

    merge_errors: list[str] = []
    superseded: list[dict] = []
    if args.merge:
        overlay, merge_errors, superseded = load_rows(args.rows_dir, records, args.tex_commit,
                                                      tex_lines, prev)
        if not args.summary:
            write_map(args.map_path, records, overlay)
            write_superseded(args.superseded, superseded, commit)
    else:
        overlay = sc.load_map(args.map_path)
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
        write_tsv(records, args.out, sha256, md5, commit)
        write_md(records, args.out_md, sha256, md5, commit, merge_errors, superseded)
        if args.key_table:
            with open(args.key_table, "w", encoding="utf-8") as fh:
                fh.write(f"Keys at manuscript commit `{commit[:9]}` (md5 `{md5}`).\n")
                fh.write(key_table(records))

    c = sc.counts(records)
    for k in sorted(c, key=lambda k: -c[k]):
        print(f"{k:14s} {c[k]:5d}")
    print(f"{'total':14s} {len(records):5d}")
    print(f"superseded     {len(superseded):5d}")
    for e in merge_errors:
        print("MERGE ERROR: " + e)
    for e in overlay_errors:
        print("OVERLAY ERROR: " + e)
    if args.check and (c.get("unassigned") or overlay_errors):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
