"""Footprint of seed types.  A seed type is an off-diagonal component T of the
pair graph C_{j+1} x_R C_{j+1}; it is a tree, and on a free (large-girth) level
a seed of type T identifies exactly |T| pairs, in |T| distinct fibres.
Reports |T| for the lawful type and the overfold types, against |C_j| and
|t_j| (the twisted-edge length), to see whether seeds are local at the scale
of Sch(Q) (bounded |T|) or only at the scale of the twisted level Q^(j).
Usage: python3 type_sizes.py jmax"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import depth_graphs, t  # noqa: E402

for j in range(int(sys.argv[1]) + 1):
    Gj, G, m = depth_graphs([0], [0], j)
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
    law, over = [], []
    for ps in comp.values():
        (law if m[ps[0][0]] == m[ps[0][1]] else over).append(len(ps))
    over.sort()
    print('j', j, '|t_j|', len(t(j)), '|C_j|', Gj.V, '|C_j+1|', V,
          'lawful |T|', law, 'overfold types', len(over),
          'overfold |T| min/median/max', over[0] if over else None,
          over[len(over) // 2] if over else None, over[-1] if over else None,
          'total overfold pairs', sum(over))
