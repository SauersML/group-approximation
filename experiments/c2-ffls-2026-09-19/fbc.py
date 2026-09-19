# G = <x,y | w>, w = yxYXXyyxYXYxYYxyXy.  Both exponent sums vanish.  With x_j = y^j x y^-j the
# relator reads r' = x_1 x_0^-2 x_2 x_1^-1 x_0 x_-2 x_-1^-1 : x_2 and x_-2 occur once, so
# G = F_4 x|_phi Z, F_4 = <x_-2,x_-1,x_0,x_1> = ker(y-exponent), phi = conjugation by y.
# Letters: p=x_-2, q=x_-1, r=x_0, s=x_1 (upper case = inverse).
import sys
INV = {c: c.swapcase() for c in 'pqrsxyPQRSXY'}
def inv(u): return ''.join(INV[c] for c in reversed(u))
def red(u):
    o = []
    for c in u:
        if o and o[-1] == INV[c]: o.pop()
        else: o.append(c)
    return ''.join(o)
W = 'yxYXXyyxYXYxYYxyXy'
# rewrite a word in x,y with y-exponent 0 into levels x_j (as a dict j->symbol string)
def levels(u):
    out = []; j = 0
    for c in u:
        if c == 'y': j += 1
        elif c == 'Y': j -= 1
        else: out.append((j, 1 if c == 'x' else -1))
    assert j == 0
    return out
PHI = {'p': 'q', 'q': 'r', 'r': 's', 's': 'rrSqPRs'}          # x_1 -> x_2 = x_0^2 x_1^-1 x_-1 x_-2^-1 x_0^-1 x_1
PHII = {'q': 'p', 'r': 'q', 's': 'r', 'p': 'QrSqqRp'}         # x_-2 -> x_-3 = x_-1^-1 x_0 x_1^-1 x_-1^2 x_0^-1 x_-2
def apply(m, u): return red(''.join(m[c] if c.islower() else inv(m[c.lower()]) for c in u))
for c in 'pqrs':
    assert apply(PHII, apply(PHI, c)) == c and apply(PHI, apply(PHII, c)) == c
def xj(j):  # x_j as a word in p,q,r,s
    base = {-2: 'p', -1: 'q', 0: 'r', 1: 's'}
    if j in base: return base[j]
    if j > 1: return apply(PHI, xj(j - 1))
    return apply(PHII, xj(j + 1))
def tofib(u):
    return red(''.join(xj(j) if e == 1 else inv(xj(j)) for j, e in levels(u)))
# check the relator: w in fibre letters is trivial
assert tofib(W) == '', tofib(W)
# Stallings folding
class Graph:
    def __init__(s): s.adj = [dict()]; 
    def add_loop(s, u):
        v = 0
        for i, c in enumerate(u):
            if i == len(u) - 1: t = 0
            else: s.adj.append(dict()); t = len(s.adj) - 1
            s.adj[v].setdefault(c, set()).add(t); s.adj[t].setdefault(INV[c], set()).add(v); v = t
    def fold(s):
        par = list(range(len(s.adj)))
        def f(v):
            while par[v] != v: par[v] = par[par[v]]; v = par[v]
            return v
        changed = True
        while changed:
            changed = False
            for v in range(len(s.adj)):
                if f(v) != v: continue
                for c, ts in list(s.adj[v].items()):
                    rs = {f(t) for t in ts}
                    if len(rs) > 1:
                        rs = sorted(rs); keep = rs[0]
                        for o in rs[1:]:
                            par[o] = keep
                            for c2, ts2 in s.adj[o].items():
                                s.adj[keep].setdefault(c2, set()).update(ts2)
                        changed = True
                    s.adj[v][c] = {f(t) for t in s.adj[v][c]}
            for v in range(len(s.adj)):
                if f(v) == v:
                    for c in s.adj[v]: s.adj[v][c] = {f(t) for t in s.adj[v][c]}
        live = sorted({f(v) for v in range(len(s.adj))})
        idx = {v: i for i, v in enumerate(live)}
        new = [dict() for _ in live]
        for v in live:
            for c, ts in s.adj[v].items():
                new[idx[v]][c] = {idx[f(t)] for t in ts}
        s.adj = new
    def stats(s):
        V = len(s.adj); E = sum(len(d) for d in s.adj) // 2
        full = sum(1 for d in s.adj if len(d) == 8)
        return V, E, E - V + 1, full
    def member(s, u):
        v = 0
        for c in u:
            if c not in s.adj[v]: return False
            v = next(iter(s.adj[v][c]))
        return v == 0
