"""Check that tree_count in first_moment.py is exact: compare with brute force for the
tree amalgam D(m_ab) *_<b> D(m_bc) and D(m_ab) *_<a> D(m_ca) (Coxeter data, n <= 6)."""
import itertools, sys
import numpy as np
from fractions import Fraction
import first_moment as fm
p, q, r = 2, 3, 7
N = 6
def compose(x, y): return tuple(x[i] for i in y)
def odiv(x, m):
    e = tuple(range(len(x))); z = e
    for _ in range(m): z = compose(x, z)
    return z == e
hs = [fm.marked_hom_counts(fm.load("D%d.dat" % m), N) for m in (p, q, r)]
swap = lambda h: [{(c2, c1): v for (c1, c2), v in hn.items()} for hn in h]
h1, h2, h3 = swap(hs[0]), hs[1], swap(hs[2])
for n in range(1, N + 1):
    invs = [x for x in itertools.permutations(range(n)) if compose(x, x) == tuple(range(n))]
    L = len(invs)
    rel = lambda m: np.array([[1 if odiv(compose(x, y), m) else 0 for y in invs] for x in invs], dtype=object)
    Mp, Mq, Mr = rel(p), rel(q), rel(r)
    brute = sum(Mp[i, j] * Mq[j].sum() * Mr[i].sum() for i in range(L) for j in range(L))
    T = fm.tree_count(h1, h2, h3, 2, 2, n)
    print(n, brute, T, brute == T)
