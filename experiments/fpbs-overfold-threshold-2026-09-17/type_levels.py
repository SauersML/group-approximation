"""Level of an overfold seed type.  For a pair (c, c') of C_{j+1} with
iota_j c != iota_j c', its level is the largest l < j such that the images of
c and c' in C_l coincide (images in C_0 = one vertex always coincide).  A
level-l overfold pair maps to a lawful pair of the depth-(l) problem
C_{l+1} -> C_l.  Reports, per depth j, the overfold types by level: count and
the list of sizes |T|, next to the lawful sizes of lower depths.
Usage: python3 type_levels.py jmax"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import depth_graphs  # noqa: E402

JMAX = int(sys.argv[1])
maps = {}
graphs = {}
for j in range(JMAX + 1):
    Gj, G, m = depth_graphs([0], [0], j)
    maps[j] = m          # C_{j+1} -> C_j
    graphs[j + 1] = G
    graphs[j] = Gj


def image(c, j, l):
    """image in C_l of a vertex c of C_{j+1}"""
    for i in range(j, l - 1, -1):
        c = maps[i][c]
    return c


for j in range(JMAX + 1):
    G = graphs[j + 1]
    V = G.V
    pairs = [(c, d) for c in range(V) for d in range(c + 1, V)]
    idx = {p: i for i, p in enumerate(pairs)}
    par = list(range(len(pairs)))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for (c, d) in pairs:
        for k in G.nb[c]:
            if k[1] == 1 and k in G.nb[d]:
                u, v = G.nb[c][k], G.nb[d][k]
                u, v = min(u, v), max(u, v)
                par[f(idx[(u, v)])] = f(idx[(c, d)])
    comp = {}
    for p in pairs:
        comp.setdefault(f(idx[p]), []).append(p)
    bylev = {}
    for ps in comp.values():
        c, d = ps[0]
        if image(c, j, j) == image(d, j, j):
            lev = 'law'
        else:
            lev = max(l for l in range(j) if image(c, j, l) == image(d, j, l))
            levs = {max(l for l in range(j) if image(x, j, l) == image(y, j, l))
                    for (x, y) in ps}
            assert levs == {lev}, levs
        bylev.setdefault(lev, []).append(len(ps))
    out = []
    for lev in ['law'] + list(range(j - 1, -1, -1)):
        if lev in bylev:
            s = sorted(bylev[lev])
            out.append((lev, len(s), s[-1], sum(s)))
    print('j', j, '(level, #types, max|T|, total pairs):', out)
