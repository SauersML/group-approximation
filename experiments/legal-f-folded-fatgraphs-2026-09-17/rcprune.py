"""Prune a column dump to the columns whose phase-1 reduced cost under the dump's own dual y is <= eps
(the columns that are (nearly) tight at y), plus the support of x.  Pruning only drops columns (a restriction of
the master); certificates are checked afresh by farkas_vmem.py.
usage: python3 rcprune.py dump.json out.json eps"""
import sys, json
import numpy as np
J = json.load(open(sys.argv[1])); eps = float(sys.argv[3])
y = np.array(J["y"]); prow = {(a, b): r for a, b, r in J["prow"]}
x = np.array(J["x"]); ci = J["colidx"]
rcs, keep = [], []
for P, j in zip(J["columns"], ci):
    s = 0.0
    for d, q in P:
        s += y[d]
        r = prow[(min(d, q), max(d, q))]
        if r < len(y):
            s += y[r] * (1.0 if d < q else -1.0)
    rc = -s
    rcs.append(rc)
    if rc <= eps or (j < len(x) and x[j] > 1e-9):
        keep.append(P)
rcs = np.array(rcs)
print("cols", len(rcs), "rc quantiles", np.quantile(rcs, [0, .01, .1, .5, .9]).round(4), "kept", len(keep))
json.dump({"columns": keep, "pruned_from": sys.argv[1], "eps": eps}, open(sys.argv[2], "w"))
