"""Non-abelian band (rung) cancellation for regular F-covers of square-tiled tori, checked step by step.

Construction of nonabelian-two-charge-torus-covers-rank-distance-linear-proof, for F = S3, Q8, A4.
Omega = G x F, b(x,a) = (x+e1, beta(x) a), c(x,a) = (x+e2, gamma(x) a).  Face x has holonomy
hol(x) = gamma(x)^-1 beta(x+e2)^-1 gamma(x+e1) beta(x); (b,c) commute iff every face is flat.

For each cover with at most two charged faces the script runs the case analysis of the proof
(single charge / neutral short pair / non-neutral short pair / long pair: path cut or strip cut),
pushes charges one step into an essential band, and closes the band by the rung lemma: it tries
every value t of the closing rung, fills the other rungs so that f_0..f_(m-2) are flat, and asserts
that some t makes f_(m-1) flat (the lemma says one always does).  It records whether the ORIGINAL
closing rung already works (the tree-only cancellation of the abelian proof), i.e. whether the
ordered charge product around the band is trivial.  It then builds the permutations, checks
commutation, computes exact ranks, and compares with a lower bound for rho (search over s,t <= M).
usage: python3 rungs.py GROUP seed ncases [Nmax [thin]]  (GROUP in S3 Q8 A4)
"""
import sys, random, itertools
from math import gcd
import numpy as np

# ---------------------------------------------------------------- groups
def closure(gens):
    n = len(gens[0]); e = tuple(range(n)); els = {e}; fr = [e]
    while fr:
        nf = []
        for x in fr:
            for g in gens:
                y = tuple(g[x[i]] for i in range(n))
                if y not in els: els.add(y); nf.append(y)
        fr = nf
    return sorted(els)

def group(name):
    if name == 'S3': P = closure([(1, 0, 2), (1, 2, 0)])
    elif name == 'A4': P = closure([(1, 2, 0, 3), (1, 0, 3, 2)])
    elif name == 'Q8':
        # quaternion units (s, u): s in {1,-1}, u in 1 i j k ; regular representation on 8 points
        U = ['1', 'i', 'j', 'k']; T = {('1', x): (1, x) for x in U}
        T.update({(x, '1'): (1, x) for x in U})
        for x in 'ijk': T[(x, x)] = (-1, '1')
        T.update({('i', 'j'): (1, 'k'), ('j', 'k'): (1, 'i'), ('k', 'i'): (1, 'j'),
                  ('j', 'i'): (-1, 'k'), ('k', 'j'): (-1, 'i'), ('i', 'k'): (-1, 'j')})
        E = [(s, u) for s in (1, -1) for u in U]
        def mul(p, q): s, u = T[(p[1], q[1])]; return (p[0] * q[0] * s, u)
        P = [tuple(E.index(mul(g, h)) for h in E) for g in E]
    else: raise ValueError(name)
    n = len(P); idx = {p: i for i, p in enumerate(P)}
    # element i acts on the set of elements by left multiplication; mul[i][j] = i*j
    comp = lambda p, q: tuple(p[q[k]] for k in range(len(p)))
    mul = [[idx[comp(P[i], P[j])] for j in range(n)] for i in range(n)]
    e = [i for i in range(n) if all(mul[i][j] == j for j in range(n))][0]
    inv = [[j for j in range(n) if mul[i][j] == e][0] for i in range(n)]
    assert any(mul[i][j] != mul[j][i] for i in range(n) for j in range(n))
    return n, mul, inv, e

# ---------------------------------------------------------------- tori
def egcd(a, b):
    if b == 0: return (a, 1, 0) if a >= 0 else (-a, -1, 0)
    g, x, y = egcd(b, a % b); return g, y, x - (a // b) * y

class Torus:
    """Z^2 / Lambda for Lambda spanned by p, q (det != 0).  Points indexed 0..N-1."""
    def __init__(self, p, q):
        d0 = p[0] * q[1] - p[1] * q[0]; assert d0 != 0
        g, x, y = egcd(p[1], q[1])                     # x p1 + y q1 = g
        self.d = g; cc = x * p[0] + y * q[0]
        self.a = abs(d0) // g; self.c = cc % self.a; self.N = self.a * self.d
        self.basis = (p, q)
        for z in (p, q): assert self.idx(z) == 0
    def red(self, z):
        x, y = z; t = y // self.d; x -= t * self.c; y -= t * self.d
        return (x % self.a, y)
    def idx(self, z):
        x, y = self.red(z); return y * self.a + x
    def pt(self, i): return (i % self.a, i // self.a)
    def vecs(self, R):
        a, c, d = self.a, self.c, self.d
        out = []
        for m2 in range(-(R // d) - 1, R // d + 2):
            for m1 in range(-(R + abs(m2) * a) // a - 2, (R + abs(m2) * a) // a + 3):
                z = (m1 * a + m2 * c, m2 * d)
                if z != (0, 0) and abs(z[0]) + abs(z[1]) <= R: out.append(z)
        return out
    def frame(self):
        R = min(self.a, self.d + self.a)
        w = min(self.vecs(R), key=lambda z: (abs(z[0]) + abs(z[1]), z))
        k = gcd(abs(w[0]), abs(w[1])); v = (w[0] // k, w[1] // k)
        g, x, y = egcd(v[0], v[1])                      # x v1 + y v2 = 1 ; det(v,u)=v1 u2 - v2 u1
        u = (-y, x); assert v[0] * u[1] - v[1] * u[0] == 1
        # reduce u so that |u|_inf is small: u -> u + j v
        u = min(((u[0] + j * v[0], u[1] + j * v[1]) for j in range(-60, 61)), key=lambda z: max(map(abs, z)))
        return w, k, v, u

def det(v, z): return v[0] * z[1] - v[1] * z[0]

# ---------------------------------------------------------------- connections
class Conn:
    """F-connection on the grid of a torus: nb, nc commuting permutations of the vertex set, edge values
    be[x] on x -> nb x and ga[x] on x -> nc x.  Face x = (x, nb x, nb nc x, nc x)."""
    def __init__(self, Gr, nb, nc, be, ga):
        self.Gr = Gr; self.nb = list(nb); self.nc = list(nc); self.be = list(be); self.ga = list(ga)
        n = len(nb); self.ib = [0] * n; self.ic = [0] * n
        for x in range(n): self.ib[nb[x]] = x; self.ic[nc[x]] = x
        assert all(nb[nc[x]] == nc[nb[x]] for x in range(n))
    def hol(self, x):
        _, mul, inv, e = self.Gr; nb, nc, be, ga = self.nb, self.nc, self.be, self.ga
        return mul[inv[ga[x]]][mul[inv[be[nc[x]]]][mul[ga[nb[x]]][be[x]]]]
    def charged(self):
        e = self.Gr[3]; return {x for x in range(len(self.nb)) if self.hol(x) != e}
    def faces_of(self, edge):
        t, y = edge                                       # ('b', y): bottom of y, top of nc^-1 y
        return (y, self.ic[y]) if t == 'b' else (y, self.ib[y])
    def get(self, edge): return self.be[edge[1]] if edge[0] == 'b' else self.ga[edge[1]]
    def set(self, edge, val):
        if edge[0] == 'b': self.be[edge[1]] = val
        else: self.ga[edge[1]] = val
    def shared(self, f, h):
        """edges shared by faces f and h"""
        out = []
        for ed in (('b', f), ('b', self.nc[f]), ('c', f), ('c', self.nb[f])):
            if h in self.faces_of(ed) and f in self.faces_of(ed) and ed not in out: out.append(ed)
        return out
    def flatten(self, f, edge):
        """reset edge (a side of face f) so that f is flat; brute force over F. Returns the value or None."""
        n, e = self.Gr[0], self.Gr[3]; old = self.get(edge)
        for val in range(n):
            self.set(edge, val)
            if self.hol(f) == e: return val
        self.set(edge, old); return None
    def push(self, f, h):
        """move the charge of face f into the adjacent face h (one edge change). Returns the edge."""
        ed = self.shared(f, h)[0]; assert self.flatten(f, ed) is not None; return ed

def grid(T):
    E1 = [T.idx((T.pt(x)[0] + 1, T.pt(x)[1])) for x in range(T.N)]
    E2 = [T.idx((T.pt(x)[0], T.pt(x)[1] + 1)) for x in range(T.N)]
    return E1, E2

def sgn(a): return (a > 0) - (a < 0)

def band_cycle(T, v, k, sigma):
    """Lemma 3 walk: the image of {sigma <= det(v,.) < sigma+|v|_1} as a closed cycle of faces with its rungs."""
    v1n = abs(v[0]) + abs(v[1]); m = k * v1n
    g, x, y = egcd(v[0], v[1]); u = (-y, x)
    z = (sigma * u[0], sigma * u[1]); assert det(v, z) == sigma
    fs, es = [], []
    for _ in range(m):
        if v[0] * v[1] == 0: st = v
        else:
            f1 = (sgn(v[1]), 0); f2 = (0, sgn(v[0]))
            st = f1 if det(v, z) - abs(v[1]) >= sigma else f2
        z2 = (z[0] + st[0], z[1] + st[1]); assert sigma <= det(v, z2) < sigma + v1n
        if st == (1, 0): ed = ('c', T.idx(z2))
        elif st == (-1, 0): ed = ('c', T.idx(z))
        elif st == (0, 1): ed = ('b', T.idx(z2))
        else: ed = ('b', T.idx(z))
        fs.append(T.idx(z)); es.append(ed); z = z2
    assert T.idx(z) == fs[0]                                   # closed
    assert len(set(fs)) == m and len(set(es)) == m             # simple
    return fs, es

def rung_close(C, fs, es):
    """Rung lemma: choose the m rung values so that every band face is flat.  Returns (ok, tree_only_ok)."""
    e = C.Gr[3]; m = len(fs); save = [C.get(ed) for ed in es]; t0 = save[-1]
    def attempt(t):
        for ed, s in zip(es, save): C.set(ed, s)
        C.set(es[-1], t)
        for i in range(m - 1):
            if C.flatten(fs[i], es[i]) is None: return False
        return all(C.hol(f) == e for f in fs)
    tree_ok = attempt(t0)
    if tree_ok: return True, True
    for t in range(C.Gr[0]):
        if attempt(t): return True, False
    return False, False

# ---------------------------------------------------------------- the construction of the proof
def band_through(T, C, v, k, x, stats):
    """single remaining charge at x (or none): close an essential band through x by rungs."""
    if not C.charged(): return
    fs, es = band_cycle(T, v, k, det(v, T.pt(x)))
    assert C.charged() <= set(fs)
    ok, tree_ok = rung_close(C, fs, es); assert ok and not C.charged()
    stats['tree_only_fails'] += (not tree_ok); stats['bands'] += 1

def path_push(T, C, x0, g):
    z = T.pt(x0); steps = [(sgn(g[0]), 0)] * abs(g[0]) + [(0, sgn(g[1]))] * abs(g[1])
    for st in steps:
        z2 = (z[0] + st[0], z[1] + st[1]); f, h = T.idx(z), T.idx(z2)
        if f != h and T.idx(z) in C.charged(): C.push(f, h)
        z = z2

def strip_cut(T, C, w, k, v, u, L, rowof, r0, r1, D, l, stats):
    """cut the row circle at r0 and r1+1, reglue each arc to Z^2/<w, H u>, push and close by rungs."""
    p, q = T.basis; dp, dq = det(v, p), det(v, q)
    gg, a1, a2 = egcd(dp, dq); assert gg == L
    lamL = (a1 * p[0] + a2 * q[0], a1 * p[1] + a2 * q[1])
    pieces = [(r0, D + 1), ((r1 + 1) % L, L - D - 1)]
    lam1 = abs(w[0]) + abs(w[1]); N = T.N
    nb, nc = [None] * N, [None] * N; be, ga = [None] * N, [None] * N
    for (s, H) in pieces:
        assert 2 * l <= H < L
        TI = Torus(w, (H * u[0], H * u[1])); assert TI.N == k * H
        P = [x for x in range(N) if (rowof[x] - s) % L < H]
        phi = {}
        for x in P:
            z = T.pt(x); t = det(v, z); m = -((t - s) // L)
            z2 = (z[0] + m * lamL[0], z[1] + m * lamL[1]); assert s <= det(v, z2) < s + H
            phi[x] = TI.idx(z2)
        assert len(set(phi.values())) == len(P) == TI.N
        inv = {y: x for x, y in phi.items()}
        E1, E2 = grid(TI)
        CI = Conn(C.Gr, E1, E2, [C.be[inv[y]] for y in range(TI.N)], [C.ga[inv[y]] for y in range(TI.N)])
        Qj = CI.charged()
        fs, es = band_cycle(TI, v, k, s - l); assert len(fs) == lam1
        bandset = set(fs)
        for y in Qj - bandset:                                  # one step into the band (Lemma 4)
            nbrs = [h for h in (E1[y], E2[y], CI.ib[y], CI.ic[y]) if h in bandset]
            assert nbrs, 'seam charge not adjacent to band'
            CI.push(y, nbrs[0]); stats['pushes'] += 1
        assert CI.charged() <= bandset
        ok, tree_ok = rung_close(CI, fs, es); assert ok and not CI.charged()
        stats['tree_only_fails'] += (not tree_ok); stats['bands'] += 1
        for x in P:
            y = phi[x]; nb[x] = inv[E1[y]]; nc[x] = inv[E2[y]]; be[x] = CI.be[y]; ga[x] = CI.ga[y]
    return Conn(C.Gr, nb, nc, be, ga)

def solve(T, C0):
    """returns (case, final connection, lam1, |g|_1, stats)"""
    C = Conn(C0.Gr, C0.nb, C0.nc, C0.be, C0.ga)
    stats = {'tree_only_fails': 0, 'bands': 0, 'pushes': 0}
    w, k, v, u = T.frame(); lam1 = abs(w[0]) + abs(w[1]); l = max(map(abs, v))
    Q = sorted(C.charged()); assert len(Q) <= 2
    if not Q: return 'flat', C, lam1, 0, stats
    if len(Q) == 1:
        band_through(T, C, v, k, Q[0], stats); return 'one', C, lam1, 0, stats
    x0, x1 = Q; d0 = (T.pt(x1)[0] - T.pt(x0)[0], T.pt(x1)[1] - T.pt(x0)[1])
    g = min([d0] + [(d0[0] + z[0], d0[1] + z[1]) for z in T.vecs(T.a + T.d + abs(d0[0]) + abs(d0[1]))],
            key=lambda z: (abs(z[0]) + abs(z[1]), z))
    g1 = abs(g[0]) + abs(g[1])
    if g1 < lam1:
        path_push(T, C, x0, g)
        if not C.charged(): return 'neutral', C, lam1, g1, stats
        assert C.charged() == {x1}
        band_through(T, C, v, k, x1, stats); return 'short', C, lam1, g1, stats
    L = T.N // k
    rowof = [det(v, T.pt(x)) % L for x in range(T.N)]
    r0, r1 = rowof[x0], rowof[x1]; D = (r1 - r0) % L
    if D > L // 2: r0, r1, D = r1, r0, L - D
    if D <= 2 * l:
        path_push(T, C, x0, g)
        if C.charged(): assert C.charged() == {x1}; band_through(T, C, v, k, x1, stats)
        return 'pathcut', C, lam1, g1, stats
    return 'strip', strip_cut(T, C, w, k, v, u, L, rowof, r0, r1, D, l, stats), lam1, g1, stats

def perms(C):
    n, mul = C.Gr[0], C.Gr[1]; N = len(C.nb)
    b = np.array([C.nb[x] * n + mul[C.be[x]][a] for x in range(N) for a in range(n)])
    c = np.array([C.nc[x] * n + mul[C.ga[x]][a] for x in range(N) for a in range(n)])
    return b, c

def cycles(p):
    seen = np.zeros(len(p), bool); cnt = 0
    for i in range(len(p)):
        if not seen[i]:
            cnt += 1; j = i
            while not seen[j]: seen[j] = True; j = p[j]
    return cnt

def rk(p, q):                                   # rank(P - Q) for permutation matrices
    pinv = np.argsort(p); return len(p) - cycles(q[pinv])

def rho_lower(b, c, M):
    binv, cinv = np.argsort(b), np.argsort(c); n = len(b); I = np.arange(n)
    bp, cp, bm, cm = [I], [I], [I], [I]
    for s in range(M):
        bp.append(b[bp[-1]]); cp.append(c[cp[-1]]); bm.append(binv[bm[-1]]); cm.append(cinv[cm[-1]])
    best = (0.0, 0, 0)
    for s in range(1, M + 1):
        for t in range(1, M + 1):
            W = cm[t][bm[s][cp[t][bp[s]]]]         # apply b^s, c^t, b^-s, c^-t
            r = n - cycles(W)
            if r / (s + t) > best[0]: best = (r / (s + t), s, t)
    return best

# ---------------------------------------------------------------- random covers with <= 2 charged faces
def random_cover(T, Gr, mode, rng):
    n, mul, inv, e = Gr; N = T.N; E1, E2 = grid(T)
    if mode == 'neutral':
        h = [rng.randrange(n) for _ in range(N)]
        be = [mul[h[E1[x]]][inv[h[x]]] for x in range(N)]; ga = [mul[h[E2[x]]][inv[h[x]]] for x in range(N)]
        C = Conn(Gr, E1, E2, be, ga); assert not C.charged()
        x0 = rng.randrange(N); z = T.pt(x0)
        gx, gy = rng.randint(-4, 4), rng.randint(-4, 4)
        if (gx, gy) == (0, 0): gx = 1
        steps = [(sgn(gx), 0)] * abs(gx) + [(0, sgn(gy))] * abs(gy)
        z2 = (z[0] + steps[0][0], z[1] + steps[0][1])
        ed = C.shared(T.idx(z), T.idx(z2))[0]; C.set(ed, rng.randrange(n))
        z = z2
        for st in steps[1:]:
            z2 = (z[0] + st[0], z[1] + st[1]); f, hh = T.idx(z), T.idx(z2)
            if f != hh and f in C.charged(): C.push(f, hh)
            z = z2
        return C
    be = [rng.randrange(n) for _ in range(N)]; ga = [rng.randrange(n) for _ in range(N)]
    C = Conn(Gr, E1, E2, be, ga)
    roots = rng.sample(range(N), 1 if mode == 'one' else 2)
    par = {r: None for r in roots}; order = list(roots); i = 0
    while i < len(order):
        x = order[i]; i += 1
        for y in (E1[x], E2[x], C.ib[x], C.ic[x]):
            if y not in par: par[y] = x; order.append(y)
    for y in reversed(order):
        if par[y] is not None and y in C.charged(): C.push(y, par[y])
    assert C.charged() <= set(roots)
    return C

def main():
    name, seed, ncases = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    Nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 24
    thin = len(sys.argv) > 5 and sys.argv[5] == 'thin'
    Gr = group(name); n = Gr[0]; rng = random.Random(seed)
    worst = 0.0; tally = {}; tf = 0; nb_bands = 0; done = 0
    while done < ncases:
        if thin: a = rng.randint(2, 4); d = rng.randint(4, Nmax // a)
        else: a = rng.randint(1, Nmax); d = rng.randint(1, max(1, Nmax // a))
        if a * d < 4: continue
        T = Torus((a, 0), (rng.randrange(a), d))
        w, k, v, u = T.frame()
        if abs(w[0]) + abs(w[1]) < 2: continue
        mode = 'pair' if thin else rng.choice(['one', 'pair', 'pair', 'neutral'])
        C0 = random_cover(T, Gr, mode, rng)
        case, C, lam1, g1, st = solve(T, C0)
        assert not C.charged()
        b, c = perms(C0); b2, c2 = perms(C)
        assert np.array_equal(b2[c2], c2[b2])
        E1, E2 = grid(T)
        sites = sum((C.nb[x], C.be[x]) != (E1[x], C0.be[x]) for x in range(T.N)) + \
                sum((C.nc[x], C.ga[x]) != (E2[x], C0.ga[x]) for x in range(T.N))
        bound = {'flat': 0, 'one': lam1, 'neutral': g1, 'short': g1 + lam1, 'pathcut': g1 + lam1,
                 'strip': 6 * lam1 + 2}[case]
        assert sites <= bound, (case, sites, bound)
        dist = max(rk(b2, b), rk(c2, c)); assert dist <= n * sites
        M = min(40, max(lam1, g1) + 4)
        rl, s, t = rho_lower(b, c, M) if case != 'flat' else (0.0, 0, 0)
        ratio = dist / rl if rl else 0.0
        if case != 'flat': assert dist <= 36 * rl, ('BOUND FAILS', case, dist, rl)
        worst = max(worst, ratio); tally[case] = tally.get(case, 0) + 1
        tf += st['tree_only_fails']; nb_bands += st['bands']; done += 1
        print(name, 'N=%d a=%d c=%d d=%d' % (T.N, T.a, T.c, T.d), 'lam1=%d g1=%d' % (lam1, g1), case,
              'sites=%d bound=%d dist=%d rho>=%.3f (s,t)=(%d,%d) ratio=%.3f treeonly_fail=%d/%d' %
              (sites, bound, dist, rl, s, t, ratio, st['tree_only_fails'], st['bands']), flush=True)
    print('SUMMARY', name, 'cases', done, tally, 'bands closed', nb_bands, 'bands where tree-only fails', tf,
          'worst dist/rho_lower %.3f' % worst)

if __name__ == '__main__':
    main()
