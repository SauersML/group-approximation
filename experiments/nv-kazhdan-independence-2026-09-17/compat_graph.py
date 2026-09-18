"""Structure of the corner compatibility graph B_k(a) of Robertson-Steger tile 2-graphs.

B_k(a): bipartite graph between (k,0)-paths and (0,k)-paths from vertex a, edge iff compatible
(some (k,k)-rectangle has both as factors).  We test whether B_k(a) is a disjoint union of
complete bipartite graphs ("biclique union"), and print its connected-component sizes.

Run from this directory:  python3 compat_graph.py
"""
import json
import sys
from collections import defaultdict

from completions import data, paths, push


def compat(T, npts, k, a):
    tiles, E1, E2, sw, out1, out2 = data(T, npts)
    L = [p for (p, _v) in paths(out1, E1, a, k)]
    M = [p for (p, _v) in paths(out2, E2, a, k)]
    adj = defaultdict(set)
    for (lam, v) in paths(out1, E1, a, k):
        for (mu2, _w) in paths(out2, E2, v, k):
            adj[lam].add(push(lam, mu2, sw))
    # components
    comp = {}
    radj = defaultdict(set)
    for lam in L:
        for mu in adj[lam]:
            radj[mu].add(lam)
    sizes = []
    biclique = True
    for lam in L:
        if ("L", lam) in comp:
            continue
        stack = [("L", lam)]
        comp[("L", lam)] = len(sizes)
        ls, ms = set(), set()
        while stack:
            side, x = stack.pop()
            (ls if side == "L" else ms).add(x)
            nb = adj[x] if side == "L" else radj[x]
            for y in nb:
                key = ("M" if side == "L" else "L", y)
                if key not in comp:
                    comp[key] = len(sizes)
                    stack.append(key)
        sizes.append((len(ls), len(ms)))
        if any(adj[x] != ms for x in ls):
            biclique = False
    return len(L), len(M), sizes, biclique


if __name__ == "__main__":
    for fn, npts in (("../nv-brick-coding-2026-09-17/tp_q2.json", 7),
                     ("../nv-brick-coding-2026-09-17/tp_q3.json", 13)):
        ex = json.load(open(fn))["examples"]
        for idx, e in enumerate(ex[:2]):
            for k in (1, 2):
                for a in (0, 1):
                    print(fn.split("/")[-1], "T%d" % idx, "k=%d a=%d" % (k, a),
                          "|L|,|M|, component sizes, biclique union =", compat(e[1], npts, k, a), flush=True)
