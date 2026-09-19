# Shared set-up for the (C2) primitive-class tests.
#   G = <x,y | w> = F_4 x|_phi <y>,  F_4 = <p,q,r,s> = <x_-2,x_-1,x_0,x_1>,  phi = conj by y.
#   H = <a,b,c,y,e>, N = H cap F_4 = < phi^k(a0,b0,c0,e0) : k in Z >.
#   c_H in H_1(N): the class of U below (= -[Q x_2] + [X_2 s x_2] - 2[pQ] - 2[qR]).
# Usage: import after putting the w11 experiment dir (fbc.py) on sys.path.
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
W11 = os.environ.get('W11DIR', os.path.join(HERE, '..', 'c2-free-by-cyclic-2026-09-18'))
sys.path.insert(0, W11)
from fbc import red, inv, apply, PHI, PHII, tofib, W

X2 = 'rrSqPRs'
U = red(inv('Q' + X2) + inv(X2) + 's' + X2 + inv('pQ') * 2 + inv('qR') * 2)
N0 = {'a0': tofib('XyxYx'), 'b0': tofib('XyyyxYYY'), 'c0': tofib('XYxyx'), 'e0': tofib('xyXY')}
XY = {'p': 'YYxyy', 'q': 'Yxy', 'r': 'x', 's': 'yxY'}

def toxy(u):
    return ''.join(XY[c] if c.islower() else inv_xy(XY[c.lower()]) for c in u)

def inv_xy(u):
    return ''.join(c.swapcase() for c in reversed(u))

def perm(cycles, n):
    p = list(range(n + 1))
    for cyc in cycles:
        for i, a in enumerate(cyc):
            p[a] = cyc[(i + 1) % len(cyc)]
    return p

class Action:
    """Right action of G on {1..n} given by images of x, y (GAP convention)."""
    def __init__(s, px, py, n):
        s.n, s.P = n, {'x': px, 'y': py}
        s.Pi = {k: [v.index(i) if i else 0 for i in range(n + 1)] for k, v in s.P.items()}
        s.F = {}  # letter of F_4 -> permutation list
        for c in 'pqrs':
            s.F[c] = [s.imgxy(XY[c], i) if i else 0 for i in range(n + 1)]
            s.F[c.upper()] = [s.F[c].index(i) if i else 0 for i in range(n + 1)]
    def imgxy(s, word, pt):
        for ch in word:
            pt = s.P[ch] [pt] if ch.islower() else s.Pi[ch.lower()][pt]
        return pt
    def img(s, word, pt):
        for ch in word:
            pt = s.F[ch][pt]
        return pt

class Schreier:
    """Schreier graph of J = Stab_{F_4}(b); free basis = non-tree edges (vertex, lower letter)."""
    def __init__(s, act, b):
        s.act, s.b = act, b
        s.tr = {b: ''}; order = [b]
        for v in order:
            for c in 'pqrsPQRS':
                t = act.F[c][v]
                if t not in s.tr:
                    s.tr[t] = s.tr[v] + c; order.append(t)
        assert len(s.tr) == act.n, 'F_4 not transitive'
        s.tree = set()
        for t, w in s.tr.items():
            if w:
                c = w[-1]; v = act.F[c.swapcase()][t]
                s.tree.add((v, c) if c.islower() else (t, c.lower()))
        s.gens = [(v, c) for v in range(1, act.n + 1) for c in 'pqrs' if (v, c) not in s.tree]
        s.idx = {g: i for i, g in enumerate(s.gens)}
        s.rank = len(s.gens)
    def word(s, g):
        v, c = g
        return red(s.tr[v] + c + inv(s.tr[s.act.F[c][v]]))
    def rewrite(s, u):
        """u in J -> list of (generator index, +-1)."""
        v, out = s.b, []
        for c in u:
            if c.islower():
                if (v, c) in s.idx: out.append((s.idx[(v, c)], 1))
                v = s.act.F[c][v]
            else:
                t = s.act.F[c][v]
                if (t, c.lower()) in s.idx: out.append((s.idx[(t, c.lower())], -1))
                v = t
        assert v == s.b, 'word not in J'
        return out
    def ab(s, u):
        vec = [0] * s.rank
        for i, e in s.rewrite(u): vec[i] += e
        return vec

def S9():
    return Action(perm([(3, 4, 6, 5), (7, 8, 9)], 9), perm([(1, 2, 3), (5, 7, 8)], 9), 9)
