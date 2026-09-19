#!/usr/bin/env python3
"""Which translation constraints does a minimal-window certificate need?

Same LP as shannon_lp.build/solve, but (T) is imposed only for translations in a
chosen set:
  all     : every p q^-1 with p, q window sites (the original LP);
  readers : only t = f f'^-1 with f, f' in F (moving one reader window onto another).
Prints both values for a list of configurations.

usage: reader_only_lp.py      (runs the built-in list: known fakes and torsion-free windows)
"""
import sys, os
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'shannon-window-certificates-2026-09-17'))
import shannon_lp
from shannon_lp import Zd, Free, solve, show

def build_T(G, E, F, mode):
    Y = list(dict.fromkeys(F))
    X = [G.one] + [G.mul(f, e) for f in Y for e in E]
    X = list(dict.fromkeys(X))
    items = [('x', g) for g in X] + [('y', g) for g in Y]
    idx = {it: i for i, it in enumerate(items)}
    n = len(items); N = 1 << n
    sites = list(dict.fromkeys(X + Y))
    if mode == 'all':
        trans = {G.mul(p, G.inv(q)) for p in sites for q in sites}
    else:
        trans = {G.mul(f, G.inv(g)) for f in Y for g in Y}
    trans.discard(G.one)
    allm = np.arange(N, dtype=np.int64)
    src, dst = [], []
    for t in trans:
        im = [idx.get((k, G.mul(t, g)), -1) for (k, g) in items]
        img = np.zeros(N, dtype=np.int64); bad = np.zeros(N, dtype=bool)
        for i in range(n):
            has = (allm >> i) & 1 == 1
            if im[i] < 0:
                bad |= has
            else:
                img |= np.where(has, 1 << im[i], 0)
        src.append(allm[~bad]); dst.append(img[~bad])
    s = np.concatenate(src) if src else np.zeros(0, dtype=np.int64)
    t_ = np.concatenate(dst) if dst else np.zeros(0, dtype=np.int64)
    gph = coo_matrix((np.ones(len(s)), (s, t_)), shape=(N, N))
    nv, col = connected_components(gph, directed=True, connection='weak')
    return dict(G=G, E=E, F=Y, X=X, Y=Y, items=items, idx=idx, n=n, col=col.astype(np.int64), nv=nv)

class Cyc:
    def __init__(self, n): self.n = n; self.one = 0
    def mul(self, u, v): return (u + v) % self.n
    def inv(self, u): return (-u) % self.n
    def show(self, u): return str(u)

CASES = [
    ('Z/3', Cyc(3), [0, 1, 2], [0, 1]),
    ('Z/5', Cyc(5), [0, 1, 2], [0, 2, 4]),
    ('Z', Zd(1), [(0,), (1,), (2,)], [(0,), (-1,), (-2,)]),
    ('Z', Zd(1), [(0,), (1,), (3,)], [(0,), (-1,), (-3,)]),
    ('Z2', Zd(2), [(0, 0), (1, 0), (0, 1)], [(0, 0), (-1, 0), (0, -1)]),
    ('Z2', Zd(2), [(0, 0), (1, 0), (0, 1)], [(0, 0), (-1, 0), (1, 1)]),
    ('F2', Free, ['', 'a', 'b'], ['', 'A', 'B']),
    ('F2', Free, ['', 'a', 'ab'], ['', 'A', 'BA']),
]

if __name__ == '__main__':
    for name, G, E, F in CASES:
        vals = []
        for mode in ('all', 'readers'):
            d = build_T(G, E, F, mode)
            res, _ = solve(d)
            vals.append('%s=%.6f(nv=%d)' % (mode, res.fun, d['nv']))
        print(name, show(G, E), show(G, F), ' '.join(vals), flush=True)
