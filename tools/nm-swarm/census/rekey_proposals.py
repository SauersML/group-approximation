#!/usr/bin/env python3
"""rekey_proposals.py <records.json> <map.tsv> <old_census.tsv> <out.tsv> [<rows files...>]

Runs ON MSI (census lane).  Reads the current extraction (records.json from
`sentence_census.py --json`), the overlay map, and the census TSV of the tex the
map was keyed to.  Writes proposals:

  STALE  old_key  best_new_key  ratio  new_line  old_sentence | new_sentence
  ROW    <rowfile> <given key>  resolved_key  new_line  status  decls  note-excerpt

A stale key's old sentence is matched to the most similar CURRENT sentence that
has no overlay row (difflib ratio on normalized text).  LINE:<n> keys of lane row
files resolve to the unique sentence of the current tex starting at line n (or a
list of candidates when several start there).
"""
import csv, difflib, json, re, sys

rec_path, map_path, old_path, out_path = sys.argv[1:5]
row_files = sys.argv[5:]
records = json.load(open(rec_path))
by_key = {r["key"]: r for r in records}

def norm(s):
    s = re.sub(r"\\[a-zA-Z]+|[{}$~\\]", " ", s)
    return re.sub(r"\s+", " ", s).strip().lower()

overlay = {}
for line in open(map_path, encoding="utf-8"):
    if not line.strip() or line.startswith("#"):
        continue
    parts = line.rstrip("\n").split("\t")
    if len(parts) >= 2:
        overlay[parts[0]] = parts

old = {}
with open(old_path, encoding="utf-8") as fh:
    for line in fh:
        if line.startswith("#") or line.startswith("key\t"):
            continue
        p = line.rstrip("\n").split("\t")
        if len(p) >= 8:
            old[p[0]] = p

unassigned = [r for r in records if r["key"] not in overlay]
out = open(out_path, "w", encoding="utf-8")
for key in sorted(set(overlay) - set(by_key)):
    osent = old.get(key, [""] * 8)[7]
    best, bestr = None, 0.0
    for r in unassigned:
        ratio = difflib.SequenceMatcher(None, norm(osent), norm(r["sentence"])).ratio()
        if ratio > bestr:
            best, bestr = r, ratio
    nk = best["key"] if best else "-"
    nl = best["line"] if best else "-"
    ns = best["sentence"][:220] if best else ""
    out.write(f"STALE\t{key}\t{nk}\t{bestr:.2f}\t{nl}\t{overlay[key][1]}\t{osent[:220]} | {ns}\n")

by_line = {}
for r in records:
    by_line.setdefault(int(r["line"]), []).append(r)
# 09-09 lane rows carry line numbers of the OLD tex (the census tex): resolve them there,
# then follow the old key into the current extraction when it survives.
old_by_line = {}
for k, p in old.items():
    try:
        old_by_line.setdefault(int(p[1]), []).append(k)
    except ValueError:
        pass
use_old_lines = any("/45937c31" in rf for rf in row_files)
for rf in row_files:
    oldlines = "/45937c31" in rf
    for line in open(rf, encoding="utf-8"):
        if not line.strip() or line.startswith("#"):
            continue
        p = line.rstrip("\n").split("\t")
        k = p[0]
        if re.match(r"^[a-z0-9-]+:(LINE:\d+|[0-9a-f]{12})$", k):
            k = k.split(":", 1)[1]
        m = re.match(r"LINE:(\d+)", k)
        if m and oldlines:
            ks = old_by_line.get(int(m.group(1)), [])
            res = ",".join((kk if kk in by_key else kk + "(stale)") for kk in ks) or "NONE"
            ln = "old:" + m.group(1)
        elif m:
            cands = by_line.get(int(m.group(1)), [])
            res = ",".join(c["key"] for c in cands) or "NONE"
            ln = m.group(1)
        else:
            res = k if k in by_key else "STALE-OR-UNKNOWN"
            ln = by_key[k]["line"] if k in by_key else "-"
        st = p[1] if len(p) > 1 else ""
        dc = p[2] if len(p) > 2 else ""
        nt = p[3][:160] if len(p) > 3 else ""
        out.write(f"ROW\t{rf.split('/')[-1]}\t{p[0]}\t{res}\t{ln}\t{st}\t{dc}\t{nt}\n")
out.close()
print("wrote", out_path)
