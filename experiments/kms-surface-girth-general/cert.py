#!/usr/bin/env python3
"""Write F_p labelling certificates for girth surfaces (lane hl-surface-girth-general).

usage: cert.py FAMILY T P i,j,... OUT.json [limit]
For each listed surface index, finds up to `limit` labellings with explore.py's solver and writes them in the
format of kms_girth_search.py (labels [k, t, s, x] with 1 <= x <= p-1; crossing a type-k side from t to s
contributes g_k^x if t < s and g_k^(-x) otherwise), plus the prime p.
"""
import sys, json, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import explore as E

fam, T, p = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
idxs = [int(x) for x in sys.argv[4].split(",")]
out = sys.argv[5]
limit = int(sys.argv[6]) if len(sys.argv) > 6 else 1
M, kinds = E.K.FAMILIES[fam]
S = E.surfaces_of(fam, T)
report = {"family": fam, "half_girths": list(M), "T": T, "p": p, "surfaces": len(S), "certificates": []}
for n in idxs:
    r = S[n]
    edges, verts = E.structure(r, T, M)
    lv = ["full"] * len(verts); act = [True] * len(verts)
    (cnt, nodes, status, first), edges, verts = E.run(fam, T, p, r, lv, act, limit, 10 ** 9)
    print("surface", n, "orientable", E.K.orientable(r, T), "solutions found", cnt, "status", status, flush=True)
    for sol in first[:limit]:
        report["certificates"].append({"surface_index": n, "orientable": E.K.orientable(r, T), "T": T, "p": p,
                                       "r0": r[0], "r1": r[1], "r2": r[2],
                                       "labels": [[k, t, s, sol[e]] for e, (k, t, s) in enumerate(edges)]})
json.dump(report, open(out, "w"))
print("wrote", out, "certificates", len(report["certificates"]))
