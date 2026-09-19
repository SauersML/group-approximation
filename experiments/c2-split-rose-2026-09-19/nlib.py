# Shared set-up for the split-basis rose of (C2).
#   G = <x,y | w> = F_4 x|_phi <y>, F_4 = <p,q,r,s>, H = <a,b,c,y,e>, N = H cap F_4.
#   Split basis B = (A, B, C, D) = (pSr, rP, sR, q) of F_4, written a,b,c,d (capitals = inverses).
# Needs the w11 experiment dir (fbc.py, fold2.py, cert.py) on sys.path: W11DIR or the sibling dir.
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
W11 = os.environ.get('W11DIR', os.path.join(HERE, '..', 'c2-free-by-cyclic-2026-09-18'))
sys.path.insert(0, W11)
from fbc import red, inv, apply, PHI, PHII, tofib
from fold2 import SG
from cert import Vgens

SPLIT = {'a': 'pSr', 'b': 'rP', 'c': 'sR', 'd': 'q'}          # new basis in old letters
SPLITI = {'p': 'Bcba', 'q': 'd', 'r': 'cba', 's': 'ccba'}     # old letters in the new basis
IL = {c: c.swapcase() for c in 'abcdABCD'}
def inv2(u): return ''.join(IL[c] for c in reversed(u))
def red2(u):
    o = []
    for c in u:
        if o and o[-1] == IL[c]: o.pop()
        else: o.append(c)
    return ''.join(o)
def toB(u): return red2(''.join(SPLITI[c] if c.islower() else inv2(SPLITI[c.lower()]) for c in u))
def fromB(u): return red(''.join(SPLIT[c] if c.islower() else inv(SPLIT[c.lower()]) for c in u))
for _c in 'abcd': assert toB(SPLIT[_c]) == _c
for _c in 'pqrs': assert fromB(SPLITI[_c]) == _c
PHIB = {c: toB(apply(PHI, SPLIT[c])) for c in 'abcd'}         # phi in the new basis
PHIBI = {c: toB(apply(PHII, SPLIT[c])) for c in 'abcd'}
def applyB(m, u): return red2(''.join(m[c] if c.islower() else inv2(m[c.lower()]) for c in u))
for _c in 'abcd': assert applyB(PHIBI, applyB(PHIB, _c)) == _c

def pw(u, j):
    for _ in range(abs(j)): u = apply(PHI if j > 0 else PHII, u)
    return u
_WIN = {}
def window(M=8):
    if M not in _WIN:
        g = SG()
        for v in Vgens(M): g.add_loop(v)
        _WIN[M] = g
    return _WIN[M]
def member(g, u):
    v = g.f(0)
    for c in u:
        if c not in g.out[v]: return False
        v = g.f(g.out[v][c])
    return v == g.f(0)
def inN(u, M=8, K=4):
    """Exact positive test: some phi^k(u), |k| <= K, lies in the window T_M, a subgroup of N."""
    g = window(M)
    return any(member(g, pw(u, k)) for k in range(-K, K + 1))

# Finite permutation representations of G in which H fixes the point `base` (right actions).
def perm(cycles, n):
    p = list(range(n + 1))
    for cyc in cycles:
        for i, a in enumerate(cyc): p[a] = cyc[(i + 1) % len(cyc)]
    return p
XY = {'p': 'YYxyy', 'q': 'Yxy', 'r': 'x', 's': 'yxY'}
def toxy(u): return ''.join(XY[c] if c.islower() else ''.join(ch.swapcase() for ch in reversed(XY[c.lower()])) for c in u)
class Rep:
    def __init__(s, px, py, n, base):
        s.n, s.base = n, base
        s.P = {'x': px, 'y': py}
        s.Pi = {k: [v.index(i) if i else 0 for i in range(n + 1)] for k, v in s.P.items()}
    def img(s, word, pt=None):
        pt = s.base if pt is None else pt
        for ch in word:
            pt = s.P[ch][pt] if ch.islower() else s.Pi[ch.lower()][pt]
        return pt
    def check(s):
        W = 'yxYXXyyxYXYxYYxyXy'
        assert all(s.img(W, i) == i for i in range(1, s.n + 1)), 'relator'
        for h in ['XyxYx', 'Xyyyx', 'XYxyx', 'y', 'xyX']: assert s.img(h) == s.base, 'H not in stabiliser'
        return s
REPS = [Rep(perm([(3, 4, 6, 5), (7, 8, 9)], 9), perm([(1, 2, 3), (5, 7, 8)], 9), 9, 4).check()]
def point(u):
    """Images of the coset N u (u a word in p,q,r,s) in all known finite covers."""
    return tuple(r.img(toxy(u)) for r in REPS)
def notN(u):
    """Exact negative test: u moves the base point in some cover containing H."""
    return any(x != r.base for x, r in zip(point(u), REPS))

def h1(g, u):
    """Class of u (in the subgroup of the folded graph g) as a sparse vector over its oriented edges.
    Two loops at the base have equal H_1-classes iff these edge-count vectors agree (graph, Z_1 = H_1)."""
    v, out = g.f(0), {}
    for c in u:
        t = g.f(g.out[v][c])
        key = (v, c, t) if c.islower() else (t, c.lower(), v)
        out[key] = out.get(key, 0) + (1 if c.islower() else -1)
        v = t
    assert v == g.f(0), 'not a loop'
    return {k: x for k, x in out.items() if x}
def addv(*pairs):
    out = {}
    for coef, vec in pairs:
        for k, x in vec.items(): out[k] = out.get(k, 0) + coef * x
    return {k: x for k, x in out.items() if x}
X2 = 'rrSqPRs'
U = red(inv('Q' + X2) + inv(X2) + 's' + X2 + inv('pQ') * 2 + inv('qR') * 2)   # a word for c_H
F1, F2, F3 = 'SpSrs', 'rP', 'QsRq'
