"""Seed types as double cosets of L_{j+1}.

C_{j+1} = Stallings core of L_{j+1} = <a, t_{j+1}> (one-point Q), iota: C_{j+1} -> C_j.
Off-diagonal components of the pair graph C_{j+1} x_R C_{j+1} are the seed
types; component of (c, c') <-> double coset L_{j+1} u_c u_{c'}^{-1} L_{j+1}.
Malnormality of L_{j+1} in L predicts every off-diagonal component is a TREE
(its pi_1 is L_{j+1} cap g L_{j+1} g^-1 = 1).  This script checks that, and
reports lawful (iota c = iota c') versus overfold components.
Usage: python3 pairtrees.py jmax
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import depth_graphs  # noqa: E402

for j in range(int(sys.argv[1]) + 1):
    Gj, G, m = depth_graphs([0], [0], j)  # Q = one point: G = C_{j+1}, Gj = C_j
    V = G.V
    pairs = [(c, d) for c in range(V) for d in range(V) if c != d]
    idx = {p: i for i, p in enumerate(pairs)}
    par = list(range(len(pairs)))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    edges = 0
    for (c, d) in pairs:
        for k in G.nb[c]:
            if k[1] == 1 and k in G.nb[d]:
                u = (G.nb[c][k], G.nb[d][k])
                edges += 1
                par[f(idx[u])] = f(idx[(c, d)])
    comp = {}
    for p in pairs:
        comp.setdefault(f(idx[p]), []).append(p)
    law = over = trees = 0
    for r, ps in comp.items():
        e = 0
        for (c, d) in ps:
            for k in G.nb[c]:
                if k[1] == 1 and k in G.nb[d]:
                    e += 1
        trees += (e == len(ps) - 1)
        if m[ps[0][0]] == m[ps[0][1]]:
            law += 1
            assert all(m[c] == m[d] for (c, d) in ps)
        else:
            over += 1
    print('j', j, '|C_{j+1}|', V, '|C_j|', Gj.V, 'ordered off-diagonal components',
          len(comp), 'lawful', law, 'overfold', over, 'trees', trees)
