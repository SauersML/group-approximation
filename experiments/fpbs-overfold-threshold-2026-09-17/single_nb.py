"""Can one neighbour fibre alone force the kernel?  For each letter k, a fibre
state pushed along k lives on Im_k = vertices of C_{j+1} with an incoming
k-edge.  If some nontrivial iota-class meets V minus Im_k for every k, no single
neighbour's state can push forward to a relation containing ker(iota).
Usage: python3 single_nb.py jmax"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import depth_graphs  # noqa: E402

for j in range(0, int(sys.argv[1]) + 1):
    Gj, G, m = depth_graphs([0], [0], j)
    cls = {}
    for v in range(G.V):
        cls.setdefault(m[v], []).append(v)
    nontriv = [c for c in cls.values() if len(c) > 1]
    sizes = sorted(len(c) for c in nontriv)
    out = []
    for k in [('a', 1), ('a', -1), ('b', 1), ('b', -1)]:
        im = {v for v in range(G.V) if (k[0], -k[1]) in G.nb[v]}
        bad = sum(1 for c in nontriv if any(v not in im for v in c))
        out.append((k[0] + ('+' if k[1] == 1 else '-'), len(im), bad))
    print('j', j, 'V', G.V, 'Vj', Gj.V, 'R', G.V - Gj.V, 'nontriv', len(nontriv),
          'sizes', {s: sizes.count(s) for s in set(sizes)}, out)
