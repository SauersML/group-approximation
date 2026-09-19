"""Staircase slit-pair swaps on square-tiled surfaces.

A pair (b, c) of permutations of d points is a square-tiled surface: b = right neighbour, c = up neighbour.
Corners of square x: 4x+0 = BL, 4x+1 = BR, 4x+2 = TR, 4x+3 = TL.  Vertices are classes of corners under
BR(x)~BL(bx), TR(x)~TL(bx), TL(x)~BL(cx), TR(x)~BR(cx).  Total excess = rank([b,c]-I) = d - #cycles.

A path state (x, k) is a directed grid edge with the square x on its LEFT:
  k=0 R: bottom edge of x (c-site at c^-1 x)      k=1 U: right edge of x (b-site at x)
  k=2 L: top edge of x    (c-site at x)            k=3 D: left edge of x  (b-site at b^-1 x)
It starts at corner (x,k) and ends at corner (x,k+1).  Moves: straight -> (f_k x, k), left -> (x, k+1),
right -> (n_k^-1 f_k x, k-1), with (f,n) = (b,c), (c,b^-1), (b^-1,c^-1), (c^-1,b) for k = 0..3.

A slit-pair swap of two paths with the same move word exchanges the two gluings at every pair of
corresponding edges: c(y1) <-> c(y2) on horizontal edges, b(y1) <-> b(y2) on vertical ones.
"""
import random, sys
from itertools import product

def inv(f):
    r = [0] * len(f)
    for x, y in enumerate(f): r[y] = x
    return r

def comp(f, g):  # f after g
    return [f[y] for y in g]

def ncycles(f):
    seen = bytearray(len(f)); n = 0
    for x in range(len(f)):
        if not seen[x]:
            n += 1; y = x
            while not seen[y]: seen[y] = 1; y = f[y]
    return n

def rank_minus_I(f): return len(f) - ncycles(f)

def excess(b, c):
    bi, ci = inv(b), inv(c)
    return rank_minus_I(comp(b, comp(c, comp(bi, ci))))

def power(f, k):
    r = list(range(len(f))); base = f[:]
    while k:
        if k & 1: r = comp(base, r)
        base = comp(base, base); k >>= 1
    return r

def profile(b, c, smax):
    """max over 1<=s,t<=smax of rank([b^s,c^t]-I)/(s+t): a lower bound for rho."""
    best = 0.0; arg = None; bi, ci = inv(b), inv(c)
    bp = [None] + [power(b, s) for s in range(1, smax + 1)]
    bip = [None] + [power(bi, s) for s in range(1, smax + 1)]
    cp = [None] + [power(c, t) for t in range(1, smax + 1)]
    cip = [None] + [power(ci, t) for t in range(1, smax + 1)]
    for s in range(1, smax + 1):
        for t in range(1, smax + 1):
            w = comp(bp[s], comp(cp[t], comp(bip[s], cip[t])))
            r = rank_minus_I(w) / (s + t)
            if r > best: best, arg = r, (s, t)
    return best, arg

class UF:
    def __init__(s, n): s.p = list(range(n))
    def f(s, x):
        while s.p[x] != x: s.p[x] = s.p[s.p[x]]; x = s.p[x]
        return x
    def u(s, x, y): s.p[s.f(x)] = s.f(y)

def vertices(b, c):
    d = len(b); uf = UF(4 * d)
    for x in range(d):
        uf.u(4*x+1, 4*b[x]+0); uf.u(4*x+2, 4*b[x]+3)
        uf.u(4*x+3, 4*c[x]+0); uf.u(4*x+2, 4*c[x]+1)
    lab = [uf.f(i) for i in range(4 * d)]
    classes = {}
    for i, v in enumerate(lab): classes.setdefault(v, []).append(i)
    return lab, classes

class Surf:
    def __init__(s, b, c):
        s.b, s.c = b, c; s.bi, s.ci = inv(b), inv(c)
        s.lab, s.cls = vertices(b, c)
        b_, c_, bi, ci = s.b, s.c, s.bi, s.ci
        s.f = [b_, c_, bi, ci]; s.ninv = [ci, b_, c_, bi]  # n_k^-1
    def step(s, st, mv):  # mv: 0 straight, 1 left, 2 right
        x, k = st
        if mv == 0: return (s.f[k][x], k)
        if mv == 1: return (x, (k + 1) & 3)
        return (s.ninv[k][s.f[k][x]], (k - 1) & 3)
    def site(s, st):  # ('b' or 'c', y) : the gluing y -> gen(y) crossed by this edge
        x, k = st
        if k == 0: return ('c', s.ci[x])
        if k == 1: return ('b', x)
        if k == 2: return ('c', x)
        return ('b', s.bi[x])
    def vstart(s, st): return s.lab[4*st[0] + st[1]]
    def vend(s, st): return s.lab[4*st[0] + ((st[1] + 1) & 3)]
    def cones(s):
        return [v for v, cl in s.cls.items() if len(cl) > 4]

def apply_swap(S, P1, P2):
    """Return (b', c') after swapping the gluings along paths P1, P2 (lists of states), or None if
    the 2L edges are not distinct."""
    sites1 = [S.site(st) for st in P1]; sites2 = [S.site(st) for st in P2]
    allsites = sites1 + sites2
    if len(set(allsites)) != len(allsites): return None
    b, c = S.b[:], S.c[:]
    for (g1, y1), (g2, y2) in zip(sites1, sites2):
        assert g1 == g2
        if g1 == 'b': b[y1], b[y2] = S.b[y2], S.b[y1]
        else: c[y1], c[y2] = S.c[y2], S.c[y1]
    return b, c

def cost(S, b2, c2):
    return (rank_minus_I(comp(S.bi, b2)), rank_minus_I(comp(S.ci, c2)))

def best_swap(S, Lmax, ex0=None, vertex=None, first=True):
    """Shortest (by edge count) slit-pair swap from a cone point that lowers the total excess.
    Exhaustive DFS over all move words of length <= Lmax (iterative deepening), all pairs of
    distinct starting sectors in the same direction at a cone vertex.  Returns
    (L, (costb, costc), newexcess, b', c', word, vertex) or None."""
    if ex0 is None: ex0 = excess(S.b, S.c)
    cones = [vertex] if vertex is not None else S.cones()
    starts = []
    for v in cones:
        secs = [(i // 4, i % 4) for i in S.cls[v]]
        for k in range(4):
            sk = [st for st in secs if st[1] == k]
            for i in range(len(sk)):
                for j in range(i + 1, len(sk)):
                    starts.append((v, sk[i], sk[j]))
    best = None
    for L in range(1, Lmax + 1):
        for v, s1, s2 in starts:
            stack = [([s1], [s2], ())]
            while stack:
                P1, P2, w = stack.pop()
                if len(P1) == L:
                    if S.vend(P1[-1]) == S.vend(P2[-1]):
                        r = apply_swap(S, P1, P2)
                        if r is not None:
                            ex = excess(*r)
                            if ex < ex0:
                                cand = (L, cost(S, *r), ex, r[0], r[1], w, v)
                                if best is None or sum(cand[1]) < sum(best[1]): best = cand
                    continue
                for mv in (0, 1, 2):
                    stack.append((P1 + [S.step(P1[-1], mv)], P2 + [S.step(P2[-1], mv)], w + (mv,)))
        if best is not None and first: return best
    return best

def greedy(b, c, Lmax, log=False):
    """Iterate cheapest shortest excess-lowering swaps until the pair commutes.  Returns
    (total cost max-rank to original, number of swaps, list of lengths) or None if stuck."""
    b0, c0 = b[:], c[:]; lens = []
    while True:
        ex = excess(b, c)
        if ex == 0: break
        S = Surf(b, c)
        r = best_swap(S, Lmax, ex)
        if r is None: return None, lens
        lens.append((r[0], r[1], ex - r[2])); b, c = r[3], r[4]
    cb = rank_minus_I(comp(inv(b0), b)); cc = rank_minus_I(comp(inv(c0), c))
    return max(cb, cc), lens

# ---------------------------------------------------------------- families
def tori(sizes):
    """Disjoint union of grid tori of sizes (w,h). Returns b0, c0."""
    b, c = [], []; off = 0
    for (w, h) in sizes:
        for j in range(h):
            for i in range(w):
                b.append(off + j*w + (i+1) % w); c.append(off + ((j+1) % h)*w + i)
        off += w*h
    return b, c

def two_torus_cross(p):
    b0, c0 = tori([(p, p), (p+1, p+1)])
    x1, x2 = 0, p*p
    b, c = b0[:], c0[:]
    b[x1], b[x2] = b0[x2], b0[x1]; c[x1], c[x2] = c0[x2], c0[x1]
    return b, c

def perturb(b0, c0, k, rng):
    """k random transpositions of b- or c-values (so dist <= k)."""
    b, c = b0[:], c0[:]; d = len(b)
    for _ in range(k):
        g = b if rng.random() < 0.5 else c
        x, y = rng.randrange(d), rng.randrange(d)
        g[x], g[y] = g[y], g[x]
    return b, c

def perturb_local(b0, c0, k, rng, radius):
    """k transpositions between points at word distance <= radius (clustered defects)."""
    b, c = b0[:], c0[:]; d = len(b)
    for _ in range(k):
        g = b if rng.random() < 0.5 else c
        x = rng.randrange(d); y = x
        for _ in range(rng.randrange(1, radius + 1)):
            y = rng.choice((b0, c0))[y]
        g[x], g[y] = g[y], g[x]
    return b, c

def cylinder_iet(lengths, perm, h):
    """One horizontal cylinder of circumference n = sum(lengths), height h; the top row is glued to
    the bottom row by the interval exchange (intervals in order `perm` on the bottom)."""
    n = sum(lengths); d = n * h
    b = [j*n + (i+1) % n for j in range(h) for i in range(n)]
    c = [0]*d
    for j in range(h - 1):
        for i in range(n): c[j*n + i] = (j+1)*n + i
    starts = [sum(lengths[:i]) for i in range(len(lengths))]
    pos = 0; T = [0]*n
    for a in perm:
        for u in range(lengths[a]): T[starts[a] + u] = pos + u
        pos += lengths[a]
    for i in range(n): c[(h-1)*n + i] = T[i]
    return b, c

def excised(n, w=None):
    """n x w torus (w defaults to n) with the square x = 0 excised into its own 1x1 torus:
    b: b0^-1 x -> b0 x, x -> x;  c: c0^-1 x -> c0 x, x -> x.  rank(b - b0) = rank(c - c0) = 1."""
    w = w or n
    b0, c0 = tori([(w, n)]); x = 0
    b, c = b0[:], c0[:]
    bx, cx = inv(b0)[x], inv(c0)[x]
    b[bx], b[x] = b0[x], x
    c[cx], c[x] = c0[x], x
    return b0, c0, b, c

def search_all(S, Lmax, ex0):
    """Exhaustive DFS over all move words of length <= Lmax from all pairs of equal-direction sectors
    at cone points; every prefix is tried (any endpoints).  Returns {L: min total cost} of lowering swaps."""
    starts = []
    for v in S.cones():
        secs = [(i // 4, i % 4) for i in S.cls[v]]
        for k in range(4):
            sk = [st for st in secs if st[1] == k]
            starts += [(sk[i], sk[j]) for i in range(len(sk)) for j in range(i+1, len(sk))]
    best = {}
    for s1, s2 in starts:
        stack = [([s1], [s2])]
        while stack:
            P1, P2 = stack.pop(); L = len(P1)
            r = apply_swap(S, P1, P2)
            if r is None: continue
            if excess(*r) < ex0:
                cst = cost(S, *r)
                if L not in best or sum(cst) < sum(best[L]): best[L] = cst
            if L < Lmax:
                for mv in (0, 1, 2): stack.append((P1 + [S.step(P1[-1], mv)], P2 + [S.step(P2[-1], mv)]))
    return best
