#!/usr/bin/env python3
"""merge_rows.py <records.json> <map.tsv> <green-md5.txt> <landed-shas.txt> <root> <out map> <out report>
                 <out existing-audit> <sha9> <overrides.tsv> <rows files, oldest first...>

Runs ON MSI in a census work dir exported from origin/main (census merge, 2026-09-11).
Merges the lanes' census rows ($NM/rows/*.tsv) into metadata/NON_MF_SENTENCE_MAP.tsv.

Keys.  A 12-hex sentence key of the current tex, or LINE:<n>.  `sentence_census.py` records only the
PARAGRAPH start line, so each sentence's own start line is located in the tex (its letters and digits,
searched in order from the previous sentence of the paragraph).  LINE:<n> resolves to
  * every sentence of a theorem-like environment when line n is its `\\begin{...}` or `\\label{...}` line
    (the row grades the statement as printed);
  * otherwise one sentence among those starting within two lines of n or spanning n: the best text match
    of the row's note against the sentence (quotes, words, longest common letter/digit run) with a clear
    margin, else the unique sentence that starts at n, else AMBIGUOUS and skipped.
`overrides.tsv` (lane<TAB>given key<TAB>replacement key) re-keys rows the lead has ruled on.

Several rows for one sentence are united: declarations and notes are joined, and the grade is `partial`
if any row says partial (a clause is missing), else formalized, else definition, else the latest status.
A later row of the same lane whose note says SUPERSEDES replaces that lane's earlier rows.

Checks.  A row naming declarations must cite a commit landed on origin/main, or name only declarations
defined at origin.  Every named declaration must be defined at origin (scripts/lean_decls.build_index):
missing names move to the note and a formalized/definition row becomes partial.  Every named
declaration's module must be COMPILED at origin: in the root import closure, or its origin bytes are in
a lane's compiled-evidence record, or some clone under $CLONES holds an olean newer than a source of the
same bytes; else a formalized/definition row becomes partial.  Existing map rows no lane row replaces get
the same compiled check and are downgraded the same way.
"""
import difflib
import hashlib
import json
import os
import re
import sys
from pathlib import Path

(rec_path, map_path, green_path, landed_path, root, out_map, out_rep, out_audit, sha9, overrides_path,
 *row_files) = sys.argv[1:]
ROOT = Path(root).resolve()
CLONES = Path(os.environ["CLONES"]) if os.environ.get("CLONES") else None
sys.path.insert(0, str(ROOT / "scripts"))
from lean_decls import build_index  # noqa: E402

STATUSES = {"formalized", "definition", "structural", "attribution", "provenance", "partial", "open"}
GRADED = {"formalized", "definition"}
STATEMENT_ENVS = {"theorem", "lemma", "corollary", "proposition", "mainthm", "definition", "conjecture",
                  "question", "problem", "claim"}

records = json.load(open(rec_path, encoding="utf-8"))
by_key = {r["key"]: r for r in records}
pos = {r["key"]: i for i, r in enumerate(records)}


def compact(s: str) -> str:
    return "".join(ch for ch in s if ch.isalnum())


def compact_prose(s: str) -> str:
    return compact(re.sub(r"\\[A-Za-z]+", "", s)).lower()


# ---- per-sentence tex start lines and spans ----
tex_lines = (ROOT / "non_mf_groups_exist.tex").read_text(encoding="utf-8").split("\n")
pieces, stream_line, line_offset = [], [], {}
off = 0
for n, raw in enumerate(tex_lines, start=1):
    c = compact(re.sub(r"(?<!\\)%.*$", "", raw))
    line_offset[n] = off
    pieces.append(c)
    stream_line.extend([n] * len(c))
    off += len(c)
stream = "".join(pieces)
start_line: dict = {}
located: dict = {}
cursor: dict = {}
for r in records:
    p = int(r["line"])
    cur = cursor.get(p, line_offset.get(p, 0))
    cs = compact(r["sentence"])
    found, width_used = -1, 0
    for width in (32, 20, 12, 6, len(cs)):
        head = cs[:width]
        if not head:
            break
        at = stream.find(head, cur)
        if at >= 0 and stream_line[at] - p <= 150:
            found, width_used = at, len(head)
            break
    if found >= 0:
        start_line[r["key"]] = stream_line[found]
        located[r["key"]] = True
        cursor[p] = found + width_used
    else:
        start_line[r["key"]] = p
        located[r["key"]] = False
end_line: dict = {}
for i, r in enumerate(records):
    nxt = records[i + 1] if i + 1 < len(records) else None
    if nxt is None:
        end_line[r["key"]] = len(tex_lines)
    elif int(nxt["line"]) == int(r["line"]):
        end_line[r["key"]] = max(start_line[nxt["key"]], start_line[r["key"]])
    else:
        end_line[r["key"]] = max(int(nxt["line"]) - 1, start_line[r["key"]])


def norm(s: str) -> str:
    s = re.sub(r"\\[a-zA-Z]+|[{}$~\\]", " ", s)
    return re.sub(r"\s+", " ", s).strip().lower()


def words(s: str) -> set:
    return set(re.findall(r"[a-z]{3,}", s.lower()))


def score(note: str, sentence: str) -> float:
    note = re.sub(r"\b(LANDED|COMPILED|compiled|probe|landed)\b.*$", "", note)
    note = re.sub(r"\b[0-9a-f]{7,40}\b", "", note)
    cs = norm(sentence)
    best = 0.0
    for q in (norm(x) for x in re.findall(r'["“]([^"”]{10,})["”]', note)):
        if q[:40] and q[:40] in cs:
            best = max(best, 1.0)
        best = max(best, difflib.SequenceMatcher(None, q, cs).ratio())
    cw = words(cs)
    if cw:
        best = max(best, len(words(norm(note)) & cw) / len(cw))
    a, b = compact_prose(note), compact_prose(sentence)
    if a and b:
        lcs = difflib.SequenceMatcher(None, a, b, autojunk=False).find_longest_match(0, len(a), 0, len(b)).size
        best = max(best, min(1.0, lcs / max(6, min(len(b), 30))))
    return best


map_lines = open(map_path, encoding="utf-8").read().split("\n")
if map_lines and map_lines[-1] == "":
    map_lines.pop()


def map_rows() -> dict:
    out = {}
    for i, line in enumerate(map_lines):
        if line.strip() and not line.startswith("#"):
            out[line.split("\t")[0]] = i
    return out


green = set()
for line in open(green_path, encoding="utf-8"):
    p = line.rstrip("\n").split("  ", 1)
    if len(p) == 2:
        green.add((p[0], p[1]))
landed = {line.split()[0] for line in open(landed_path, encoding="utf-8") if line.strip()}
overrides = {}
if os.path.exists(overrides_path):
    for line in open(overrides_path, encoding="utf-8"):
        p = line.rstrip("\n").split("\t")
        if len(p) >= 3 and not line.startswith("#"):
            overrides[(p[0], p[1])] = p[2]

index = build_index(ROOT)


def relpath(path) -> str:
    p = Path(path)
    if not p.is_absolute():
        p = ROOT / p
    try:
        return str(p.resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


closure: set = set()
todo = ["GroupApproximation"]
while todo:
    mod = todo.pop()
    if mod in closure:
        continue
    f = ROOT / (mod.replace(".", "/") + ".lean")
    if not f.exists():
        continue
    closure.add(mod)
    for m in re.finditer(r"^\s*import\s+([^\n]+)$", f.read_text(encoding="utf-8"), re.M):
        for tok in m.group(1).split():
            if tok.startswith("GroupApproximation."):
                todo.append(tok)


def md5_of(f: Path) -> str:
    return hashlib.md5(f.read_bytes()).hexdigest()


compiled_cache: dict = {}
evidence_how: dict = {}


def compiled(rp: str) -> bool:
    if rp in compiled_cache:
        return compiled_cache[rp]
    mod = rp[:-5].replace("/", ".") if rp.endswith(".lean") else rp
    ok, how = False, ""
    f = ROOT / rp
    if mod in closure:
        ok, how = True, "root closure"
    elif f.exists():
        h = md5_of(f)
        if (h, rp) in green:
            ok, how = True, "lane record"
        elif CLONES is not None and CLONES.is_dir():
            for c in sorted(CLONES.iterdir()):
                s = c / rp
                o = c / ".lake" / "build" / "lib" / "lean" / (rp[:-5] + ".olean")
                try:
                    if s.is_file() and o.is_file() and o.stat().st_mtime > s.stat().st_mtime and md5_of(s) == h:
                        ok, how = True, "clone olean " + c.name
                        break
                except OSError:
                    continue
    compiled_cache[rp], evidence_how[rp] = ok, how
    return ok


def env_statement_keys(n: int):
    if not 1 <= n <= len(tex_lines):
        return None
    begin = None
    for back in (0, 1, 2):
        if n - back < 1:
            break
        t = tex_lines[n - back - 1].strip()
        m = re.match(r"^\\begin\{([A-Za-z*]+)\}", t)
        if m:
            begin = (n - back, m.group(1).rstrip("*"))
            break
        if back == 0 and not re.match(r"^\\label\{", t):
            return None
    if begin is None or begin[1] not in STATEMENT_ENVS:
        return None
    b, env = begin
    end = next((i for i in range(b, len(tex_lines) + 1) if "\\end{" + env in tex_lines[i - 1]), None)
    if end is None:
        return None
    keys = [r["key"] for r in records if located[r["key"]] and b <= start_line[r["key"]] <= end]
    return keys or None


def resolve(lane: str, given: str, note: str):
    k = overrides.get((lane, given), given)
    how0 = "override %s->%s " % (given, k) if k != given else ""
    m = re.match(r"^[a-z0-9-]+:(LINE:\d+|[0-9a-f]{12})$", k)
    if m:
        k = m.group(1)
    if re.fullmatch(r"[0-9a-f]{12}", k):
        return ([k], how0 + "key") if k in by_key else ([], how0 + "STALE-KEY")
    m = re.fullmatch(r"LINE:(\d+)", k)
    if not m:
        return [], how0 + "BAD-KEY"
    n = int(m.group(1))
    env_keys = env_statement_keys(n)
    if env_keys:
        return env_keys, how0 + "statement-env"
    cands = [r["key"] for r in records
             if (located[r["key"]] and abs(start_line[r["key"]] - n) <= 2)
             or start_line[r["key"]] <= n <= end_line[r["key"]]]
    cands = list(dict.fromkeys(cands))
    named = [x for x in re.findall(r"\b[0-9a-f]{12}\b", note) if x in by_key]
    if len(set(named)) == 1 and abs(start_line[named[0]] - n) <= 15:
        return [named[0]], how0 + "note-key"
    if not cands:
        return [], how0 + "NO-SENTENCE-NEAR-LINE"
    if len(cands) == 1:
        return cands, how0 + "only-candidate"
    scored = sorted(((score(note, by_key[c]["sentence"]) + (0.2 if located[c] and start_line[c] == n else 0.0), c)
                     for c in cands), reverse=True)
    if scored[0][0] >= 0.5 and scored[0][0] - scored[1][0] >= 0.1:
        return [scored[0][1]], how0 + "match %.2f>%.2f" % (scored[0][0], scored[1][0])
    at_n = [c for c in cands if located[c] and start_line[c] == n]
    if len(at_n) == 1:
        return at_n, how0 + "starts-at-line"
    return [], how0 + "AMBIGUOUS " + " ".join("%s@%d:%.2f" % (c, start_line[c], s) for s, c in scored)


def clean(x) -> str:
    return re.sub(r"\s+", " ", str(x)).strip()


report = [["action", "lane", "given", "key", "start_line", "old_status", "new_status", "how", "reasons",
           "sentence", "row_note"]]
groups: dict = {}
order = 0
for rf in row_files:
    lane = Path(rf).stem
    for line in open(rf, encoding="utf-8"):
        if not line.strip() or line.startswith("#"):
            continue
        p = line.rstrip("\n").split("\t")
        while len(p) < 4:
            p.append("")
        if re.search(r"@(SHA|TAG)@", p[3]):
            report.append(["SKIP", lane, p[0], "-", "-", "-", p[1], "staged template", "placeholder @SHA@/@TAG@: "
                           "the row waits for a landing", "", clean(p[3])[:220]])
            continue
        keys, how = resolve(lane, p[0].strip(), p[3])
        if not keys:
            report.append(["SKIP", lane, p[0], "-", "-", "-", p[1], how, "", "", clean(p[3])[:220]])
            continue
        for key in keys:
            order += 1
            g = groups.setdefault(key, [])
            if "SUPERSEDES" in p[3]:
                g[:] = [x for x in g if x[0] != lane]
            g.append((lane, p, how, order))

idx = map_rows()
old_cols = {k: map_lines[i].split("\t") for k, i in idx.items()}
new_rows: dict = {}
downgrades = 0
for key, g in groups.items():
    old = old_cols.get(key)
    old_status = old[1] if old and len(old) > 1 else "-"
    sent = by_key[key]["sentence"][:160]
    statuses = [x[1][1].strip() for x in g]
    bad = [s for s in statuses if s not in STATUSES]
    if bad:
        report.append(["SKIP", ",".join(x[0] for x in g), ",".join(x[1][0] for x in g), key, start_line[key],
                       old_status, ",".join(statuses), "; ".join(x[2] for x in g), "unknown status", sent, ""])
        continue
    if "partial" in statuses:
        status = "partial"
    elif "formalized" in statuses:
        status = "formalized"
    elif "definition" in statuses:
        status = "definition"
    else:
        status = statuses[-1]
    decls, notes, reasons, skip = [], [], [], False
    for lane, p, how, _ in g:
        ds = p[2].split()
        note = clean(p[3])
        if ds and not (set(re.findall(r"\b[0-9a-f]{7,40}\b", note)) & landed):
            if all(d in index and compiled(relpath(index[d])) for d in ds):
                reasons.append("rows/%s.tsv cites no landed commit; its declarations are defined and compiled at "
                               "origin" % lane)
            else:
                report.append(["SKIP", lane, p[0], key, start_line[key], old_status, p[1], how,
                               "cites no commit landed on origin/main and its declarations are not all defined and "
                               "compiled at origin", sent, note[:220]])
                continue
        for d in ds:
            if d not in decls:
                decls.append(d)
        notes.append("rows/%s.tsv: %s" % (lane, note))
    if not notes:
        continue
    missing = [d for d in decls if d not in index]
    if missing:
        decls = [d for d in decls if d in index]
        reasons.append("not defined at origin %s: %s" % (sha9, " ".join(missing)))
    notcomp = sorted({relpath(index[d]) for d in decls if not compiled(relpath(index[d]))})
    if notcomp:
        reasons.append("carrier not compiled at origin %s (no root closure, lane record, or clone olean of these "
                       "bytes): %s" % (sha9, " ".join(x[:-5].replace("/", ".") for x in notcomp)))
    new_status = status
    if (missing or notcomp) and status in GRADED:
        new_status = "partial"
        downgrades += 1
    newnote = "%s [census merge %s]" % (" | ".join(notes), sha9)
    if missing or notcomp:
        newnote += (" DOWNGRADED from %s: " % status if new_status != status else " NOTE: ") + "; ".join(
            r for r in reasons if not r.startswith("rows/"))
    row = "\t".join([key, new_status, " ".join(decls), newnote])
    if old and old[1:3] == [new_status, " ".join(decls)]:
        action = "SAME-GRADE"
    elif old:
        action = "REPLACE"
    else:
        action = "ADD"
    if len(g) > 1:
        action += "+UNION%d" % len(g)
    new_rows[key] = row
    report.append([action, ",".join(dict.fromkeys(x[0] for x in g)), ",".join(x[1][0] for x in g), key,
                   start_line[key], old_status, new_status, "; ".join(dict.fromkeys(x[2] for x in g)),
                   "; ".join(reasons), sent, newnote[:300]])

for key, row in new_rows.items():
    if key in idx:
        map_lines[idx[key]] = row
for key in sorted((k for k in new_rows if k not in idx), key=lambda k: pos[k]):
    cur = map_rows()
    anchors = [(pos[k2], i) for k2, i in cur.items() if k2 in pos and pos[k2] < pos[key]]
    if anchors:
        at = max(anchors)[1] + 1
    else:
        at = max((i for i, line in enumerate(map_lines) if line.startswith("#")), default=-1) + 1
    map_lines.insert(at, new_rows[key])

audit = [["key", "start_line", "old_status", "new_status", "not-compiled carrier modules"]]
existing_downgrades = 0
restored = 0
DOWN_SUFFIX = re.compile(r" \[census merge [0-9a-f]+: DOWNGRADED from (formalized|definition): carrier not compiled at "
                         r"origin \(no root closure, lane record, or clone olean of these bytes\): [^\]]*\]$")
for key, i in map_rows().items():
    if key in new_rows or key not in by_key:
        continue
    cols = map_lines[i].split("\t")
    while len(cols) < 4:
        cols.append("")
    m = DOWN_SUFFIX.search(cols[3])
    if cols[1] == "partial" and m:
        still = sorted({relpath(index[d]) for d in cols[2].split() if d in index and not compiled(relpath(index[d]))})
        if not still and all(d in index for d in cols[2].split()):
            audit.append([key, str(start_line[key]), "partial", m.group(1), "RESTORED: carriers now compiled"])
            cols[1] = m.group(1)
            cols[3] = cols[3][:m.start()]
            map_lines[i] = "\t".join(cols)
            restored += 1
        continue
    if cols[1] not in GRADED:
        continue
    badm = sorted({relpath(index[d]) for d in cols[2].split() if d in index and not compiled(relpath(index[d]))})
    if badm:
        mods = " ".join(x[:-5].replace("/", ".") for x in badm)
        audit.append([key, str(start_line[key]), cols[1], "partial", mods])
        cols[3] = "%s [census merge %s: DOWNGRADED from %s: carrier not compiled at origin (no root closure, lane " \
                  "record, or clone olean of these bytes): %s]" % (cols[3], sha9, cols[1], mods)
        cols[1] = "partial"
        map_lines[i] = "\t".join(cols)
        existing_downgrades += 1

with open(out_map, "w", encoding="utf-8") as fh:
    fh.write("\n".join(map_lines) + "\n")
with open(out_rep, "w", encoding="utf-8") as fh:
    for r in report:
        fh.write("\t".join(clean(x) for x in r) + "\n")
with open(out_audit, "w", encoding="utf-8") as fh:
    for r in audit:
        fh.write("\t".join(r) + "\n")
    fh.write("# compiled evidence used: " + " ".join("%s=%s" % (k, v) for k, v in sorted(evidence_how.items()) if v) + "\n")

counts: dict = {}
for r in report[1:]:
    counts[r[0]] = counts.get(r[0], 0) + 1
print("merge", sha9, "sentences with lane rows", len(groups), "actions", counts, "downgraded merged", downgrades,
      "downgraded existing", existing_downgrades, "restored existing", restored, "sentences located", sum(located.values()), "of", len(records),
      "root closure modules", len(closure))
