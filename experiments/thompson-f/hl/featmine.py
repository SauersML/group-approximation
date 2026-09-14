#!/usr/bin/env python3
"""Mine membership rules for optimal doubling sets Y inside U = M_{D,L} (Thompson's F positive monoid).

For each feature family and window k, group U by the feature key and pick the best 0/1 rule
(key in Y iff majority). Report the mismatch count and rate. A family with mismatch 0 at small k
means the optimal set is defined by that local feature.
usage: featmine.py CERTFILE D L
"""
import sys, itertools
from collections import defaultdict

cert, D, L = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
Y = set()
for line in open(cert):
    line = line.strip()
    if line:
        Y.add(tuple(int(x) for x in line.split(",")))

def clip(v, lo, hi):
    return lo if v < lo else hi if v > hi else v

def feats(w, k):
    c = [w[p] - p for p in range(D)]
    gaps = [w[p + 1] - w[p] for p in range(D - 1)]
    out = {}
    out["cpre"] = tuple(clip(x, -3, 6) for x in c[:k])
    out["tailL"] = tuple(clip(L - w[D - 1 - i], 0, 8) for i in range(min(k, D)))
    out["gpre"] = tuple(clip(x, 0, 4) for x in gaps[:k])
    out["gsuf"] = tuple(clip(x, 0, 4) for x in gaps[::-1][:k]) + (clip(L - w[-1], 0, 6),)
    # c from the right end, relative to the maximal allowed c at that position (L - p)
    out["csuf"] = tuple(clip((L - p) - w[p], 0, 8) for p in range(D - 1, max(-1, D - 1 - k), -1))
    half = (k + 1) // 2
    out["both"] = out["cpre"][:half] + ("|",) + out["csuf"][:half]
    # records of c with value <= 3 (positions and values), clipped window
    rec = []; mx = -10**9
    for p, x in enumerate(c):
        if x > mx:
            if x <= 3:
                rec.append((min(p, k), x))
            mx = x
    out["records"] = tuple(rec)
    return out

U = list(itertools.combinations_with_replacement(range(L + 1), D))
print("D", D, "L", L, "|U|", len(U), "|Y|", len(Y), "frac", round(len(Y) / len(U), 4))
fams = ["cpre", "tailL", "gpre", "gsuf", "csuf", "both", "records"]
for k in range(1, min(D, 9) + 1):
    counts = {f: defaultdict(lambda: [0, 0]) for f in fams}
    for w in U:
        inY = w in Y
        fs = feats(w, k)
        for f in fams:
            counts[f][fs[f]][1 if inY else 0] += 1
    row = []
    for f in fams:
        mism = sum(min(a, b) for a, b in counts[f].values())
        row.append("%s:%d(%.3f,keys=%d)" % (f, mism, mism / len(U), len(counts[f])))
    print("k=%d " % k + " ".join(row))
    sys.stdout.flush()
print("DONE")
