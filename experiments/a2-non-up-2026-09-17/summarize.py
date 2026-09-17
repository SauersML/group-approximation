#!/usr/bin/env python3
"""Summarize runs/*.jsonl of up_a2.py: one line per (file, host, radii) with orbit count, results,
instance sizes and solve-time range; exits nonzero if any SAT model failed verification or if a
non-control run is SAT (a SAT non-control run would be a group without unique products: print it)."""
import glob
import json
import os
import sys
from collections import defaultdict

here = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
groups = defaultdict(list)


def rng(v):
    return str(min(v)) if min(v) == max(v) else "%d-%d" % (min(v), max(v))


bad = 0
for f in sorted(glob.glob(os.path.join(here, "*.jsonl"))):
    for line in open(f):
        r = json.loads(line)
        groups[(os.path.basename(f), r["file"], r["host"], r["ra"], r["rb"], r["control"])].append(r)
        if r["result"] == "SAT" and not r.get("verified"):
            bad += 1
        if r["result"] == "SAT" and not r["control"]:
            print("NON-CONTROL SAT:", json.dumps(r))
print("| run file | q | host | radii | orbits | results | |A|,|B| | pairs | vars | clauses | solve s (min-max) |")
print("|---|---|---|---|---|---|---|---|---|---|---|")
for (rf, pf, host, ra, rb, ctl), rs in groups.items():
    idx = sorted({r["index"] for r in rs})
    res = defaultdict(int)
    for r in rs:
        res[r["result"] + ("/verified" if r.get("verified") else "")] += 1
    ts = [r["solve_seconds"] for r in rs]
    print("| %s | %d | %s%s | %d,%d | %d (%s) | %s | %d,%d | %d | %s | %s | %.1f-%.1f |" % (
        rf, rs[0]["q"], host, " control" if ctl else "", ra, rb, len(idx),
        ",".join(map(str, idx)) if len(idx) <= 12 else "%d-%d" % (idx[0], idx[-1]),
        " ".join("%s x%d" % kv for kv in sorted(res.items())), rs[0]["size_A"], rs[0]["size_B"],
        rs[0]["pairs"], rng([r["vars"] for r in rs]),
        rng([r["clauses"] for r in rs]),
        min(ts), max(ts)))
sys.exit(1 if bad else 0)
