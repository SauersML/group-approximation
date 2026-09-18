"""Many-charge F-covers of square-tiled tori: box clusters + pushes (thick case) and the row strip cut
at every charged row group (thin case), checked step by step.

Construction of regular-torus-covers-rank-distance-polynomial-in-profile-proof.  Uses rungs.py (same directory)
for tori, connections, bands and the rung lemma.

Omega = G x Y with b(x,y) = (x+e1, beta(x).y), c(x,y) = (x+e2, gamma(x).y), beta, gamma : G -> F, and F acting
on Y.  Regular covers: Y = F by left multiplication (S3, Q8, A4).  Non-free covers: S3 on 3 points, S4 on 4
points (Y-mode, Theorem B of the node).

For each random cover with n charged faces the script
  * Construction B (box clusters): for theta = 1, 2, ... forms the box clusters at threshold theta (merge two
    clusters when their lifted bounding boxes are within l_inf distance theta), and at the first theta with
    4 n theta <= lambda_1 at which every cluster is neutral, pushes every charge of each cluster to the corner of
    its bounding box (Lemma 3 of the two-charge proof).  It asserts the result is flat, sites <= 2 n^2 theta,
    and weighted cost sum supp(old^-1 new) <= 2 theta n sum_C k_C S_C.
    For every theta tried, every NON-neutral cluster C is checked against the box-count lemma:
    rank([b^s,c^t]-I) >= (1/2) (theta+1)^2 |supp hol(dP_C)| with s = w_C+theta, t = h_C+theta.
  * Construction A (strip cut, every mode): groups the charged rows (gaps > 2l split groups), cuts the row
    circle at the first row of every group, reglues each piece to Z^2/<w, H u>, walks every charge along f
    (det(v,f) = -l) into the digital band B_(s'-l), and closes the band by rungs.  Asserts flatness and
    sites <= 3 p lambda_1 + (2n+1) n (p = number of pieces; p = 1: lambda_1 + (2n+1) n).
Then it computes exact rank distances of both outputs, a lower bound rho_lower for rho (s,t <= M), and asserts
    dist <= |Y| * sites for both outputs, weighted cost bound for B, and the theorem bounds with rho_lower in
    place of rho (stronger than the theorems, since rho_lower <= rho):
    regular mode: dist <= 10240 rho_lower^4 / |F|^3;   every mode: dist <= 608 rho_lower^4 (rho_lower + |Y|).
usage: python3 multicharge.py GROUP seed ncases [Nmax [nmax]]   GROUP in S3 Q8 A4 S3on3 S4on4
"""
import sys, os, random
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rungs import closure, group, Torus, Conn, grid, band_cycle, rung_close, det, egcd, sgn, cycles, rk

def ygroup(name):
    """returns (Gr, act, regular): Gr = (n, mul, inv, e) as in rungs.py, act[g][y] the action on Y."""
    if name in ('S3', 'Q8', 'A4'):
        Gr = group(name); return Gr, Gr[1], True
    if name == 'S3on3': P = closure([(1, 0, 2), (1, 2, 0)])
    elif name == 'S4on4': P = closure([(1, 0, 2, 3), (1, 2, 3, 0)])
    else: raise ValueError(name)
    n = len(P); idx = {p: i for i, p in enumerate(P)}
    comp = lambda p, q: tuple(p[q[k]] for k in range(len(p)))
    mul = [[idx[comp(P[i], P[j])] for j in range(n)] for i in range(n)]
    e = idx[tuple(range(len(P[0])))]
    inv = [[j for j in range(n) if mul[i][j] == e][0] for i in range(n)]
    return (n, mul, inv, e), [list(p) for p in P], False

def supp(act, g): return sum(act[g][y] != y for y in range(len(act[0])))

def perms(C, act):
    m = len(act[0]); N = len(C.nb)
    b = np.array([C.nb[x] * m + act[C.be[x]][a] for x in range(N) for a in range(m)])
    c = np.array([C.nc[x] * m + act[C.ga[x]][a] for x in range(N) for a in range(m)])
    return b, c

def comm_rank(b, c, s, t):
    binv, cinv = np.argsort(b), np.argsort(c); W = np.arange(len(b))
    for _ in range(s): W = b[W]
    for _ in range(t): W = c[W]
    for _ in range(s): W = binv[W]
    for _ in range(t): W = cinv[W]
    return len(b) - cycles(W)

def rho_lower(b, c, M):
    binv, cinv = np.argsort(b), np.argsort(c); n = len(b); I = np.arange(n)
    bp, cp, bm, cm = [I], [I], [I], [I]
    for s in range(M):
        bp.append(b[bp[-1]]); cp.append(c[cp[-1]]); bm.append(binv[bm[-1]]); cm.append(cinv[cm[-1]])
    best = 0.0
    for s in range(1, M + 1):
        for t in range(1, M + 1):
            W = cm[t][bm[s][cp[t][bp[s]]]]
            best = max(best, (n - cycles(W)) / (s + t))
    return best

# ---------------------------------------------------------------- rectangles and box clusters
def rect_hol(T, C, z, s, t):
    """holonomy of the boundary of the s x t box of faces with lower-left face z (counterclockwise from z)."""
    _, mul, inv, _ = C.Gr; h = C.Gr[3]; x, y = z
    for _ in range(s): h = mul[C.be[T.idx((x, y))]][h]; x += 1
    for _ in range(t): h = mul[C.ga[T.idx((x, y))]][h]; y += 1
    for _ in range(s): x -= 1; h = mul[inv[C.be[T.idx((x, y))]]][h]
    for _ in range(t): y -= 1; h = mul[inv[C.ga[T.idx((x, y))]]][h]
    return h

def bbox(P):
    xs = [p[0] for p in P]; ys = [p[1] for p in P]
    return min(xs), min(ys), max(xs) - min(xs) + 1, max(ys) - min(ys) + 1

def box_dist(A, B):
    ax, ay, aw, ah = A; bx, by, bw, bh = B
    dx = max(0, bx - (ax + aw - 1), ax - (bx + bw - 1)); dy = max(0, by - (ay + ah - 1), ay - (by + bh - 1))
    return max(dx, dy)

def box_clusters(T, Q, theta, lam1):
    """planar box clustering of the lifted charges at threshold theta; clusters are lists of lifted points."""
    vec = [(0, 0)] + T.vecs(2 * lam1 + 4 * theta + 4)
    cl = [[T.pt(q)] for q in Q]
    changed = True
    while changed:
        changed = False
        for i in range(len(cl)):
            A = bbox(cl[i])
            for lv in vec[1:]:                               # a cluster must not touch its own translate
                assert box_dist(A, (A[0] + lv[0], A[1] + lv[1], A[2], A[3])) > theta, 'wrap'
            for j in range(i + 1, len(cl)):
                B = bbox(cl[j])
                for lv in vec:
                    if box_dist(A, (B[0] + lv[0], B[1] + lv[1], B[2], B[3])) <= theta:
                        cl[i] = cl[i] + [(p[0] + lv[0], p[1] + lv[1]) for p in cl[j]]; del cl[j]
                        changed = True; break
                if changed: break
            if changed: break
    return cl

def copyc(C): return Conn(C.Gr, C.nb, C.nc, C.be, C.ga)

def construction_B(T, C0, act, lam1, b, c, stats):
    """returns (theta, final connection, sites, weighted cost) or None if no admissible theta is neutral."""
    Q = sorted(C0.charged()); n = len(Q); e = C0.Gr[3]
    theta = 1
    while 4 * n * theta <= lam1:
        R = T.a + T.d + 4 * n * theta + 4
        cl = box_clusters(T, Q, theta, R)
        allneutral = True
        for P in cl:
            x0, y0, w, h = bbox(P)
            assert w <= len(P) * theta and h <= len(P) * theta
            H = rect_hol(T, C0, (x0, y0), w, h)
            if H != e:
                allneutral = False
                # box-count lemma: (theta+1)^2 boxes of size (w+theta) x (h+theta) around P_C, each W conj H
                s, t = w + theta, h + theta
                for i in range(theta + 1):
                    for j in range(theta + 1):
                        assert supp(act, rect_hol(T, C0, (x0 - i, y0 - j), s, t)) == supp(act, H)
                r = comm_rank(b, c, s, t)
                assert 2 * r >= (theta + 1) ** 2 * supp(act, H), ('box count', r, theta, supp(act, H))
                stats['boxcount_checks'] += 1
        if allneutral:
            C = copyc(C0); cost = 0; sites = 0; bound_w = 0
            for P in cl:
                x0, y0, w, h = bbox(P)
                SC = sum(supp(act, C0.hol(T.idx(p))) for p in P); bound_w += len(P) * SC
                for p in P:                                   # monotone path from p to the corner (x0, y0)
                    z = p; steps = [(-1, 0)] * (p[0] - x0) + [(0, -1)] * (p[1] - y0)
                    for st in steps:
                        z2 = (z[0] + st[0], z[1] + st[1]); f, g = T.idx(z), T.idx(z2)
                        if f in C.charged():
                            ed = C.shared(f, g)[0]; old = C.get(ed); C.push(f, g)
                            cost += supp(act, C.Gr[1][C.Gr[2][old]][C.get(ed)]); sites += 1
                        z = z2
            assert not C.charged(), 'neutral clusters did not vanish'
            assert sites <= 2 * n * n * theta
            assert cost <= 2 * theta * n * bound_w
            return theta, C, sites, cost
        theta += 1
    return None

def walk_into(TI, CI, y, f, bandset, cap):
    """walk the charge at face y along f until it enters the band; returns number of pushes."""
    steps = 0; z = TI.pt(y)
    while TI.idx(z) not in bandset:
        z2 = (z[0] + f[0], z[1] + f[1]); a, g = TI.idx(z), TI.idx(z2)
        if a in CI.charged(): CI.push(a, g); steps += 1
        z = z2; assert steps <= cap + 1
    return steps

def construction_A(T, C0, stats):
    """row strip cut at every charged-row group; returns (final connection, sites, p)."""
    C = copyc(C0); N = T.N
    w, k, v, u = T.frame(); lam1 = abs(w[0]) + abs(w[1]); l = max(map(abs, v)); L = N // k
    if l == abs(v[0]): f = (0, -sgn(v[0]))
    else: f = (sgn(v[1]), 0)
    assert det(v, f) == -l
    rowof = [det(v, T.pt(x)) % L for x in range(N)]
    Q = sorted(C.charged()); n = len(Q)
    rows = sorted(set(rowof[q] for q in Q)); qn = len(rows)
    gaps = [((rows[(i + 1) % qn] - rows[i]) % L) or L for i in range(qn)]
    starts = [rows[(i + 1) % qn] for i in range(qn) if gaps[i] > 2 * l]
    if len(starts) <= 1:                                   # no cut: push everything into one band of G
        s0 = starts[0] if starts else rows[0]
        fs, es = band_cycle(T, v, k, s0 - l); bandset = set(fs); tot = 0
        for q in Q:
            if q in C.charged() and q not in bandset:
                st = walk_into(T, C, q, f, bandset, 2 * n + 1); assert st <= 2 * n + 1; tot += st
        assert C.charged() <= bandset
        ok, _ = rung_close(C, fs, es); assert ok and not C.charged()
        sites = sum(C.be[x] != C0.be[x] for x in range(N)) + sum(C.ga[x] != C0.ga[x] for x in range(N))
        assert sites <= lam1 + (2 * n + 1) * n
        return C, sites, 1
    p, q_ = T.basis; dp, dq = det(v, p), det(v, q_)
    gg, a1, a2 = egcd(dp, dq); assert gg == L
    lamL = (a1 * p[0] + a2 * q_[0], a1 * p[1] + a2 * q_[1])
    starts = sorted(starts); pieces = []
    for i, s in enumerate(starts):
        H = (starts[(i + 1) % len(starts)] - s) % L; pieces.append((s, H))
    assert sum(H for _, H in pieces) == L
    nb, nc, be, ga = [None] * N, [None] * N, [None] * N, [None] * N
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
        kj = sum(1 for q in Q if q in phi)
        fs, es = band_cycle(TI, v, k, s - l); bandset = set(fs); assert len(fs) == lam1
        tot = 0
        for y in sorted(CI.charged()):
            if y in CI.charged() and y not in bandset:
                tot += walk_into(TI, CI, y, f, bandset, 2 * n + 1)
        assert CI.charged() <= bandset
        assert tot <= lam1 + (2 * n + 1) * kj, (tot, lam1, n, kj)
        ok, _ = rung_close(CI, fs, es); assert ok and not CI.charged()
        for x in P:
            y = phi[x]; nb[x] = inv[E1[y]]; nc[x] = inv[E2[y]]; be[x] = CI.be[y]; ga[x] = CI.ga[y]
    CF = Conn(C.Gr, nb, nc, be, ga)
    E1, E2 = grid(T)
    sites = sum((CF.nb[x], CF.be[x]) != (E1[x], C0.be[x]) for x in range(N)) + \
            sum((CF.nc[x], CF.ga[x]) != (E2[x], C0.ga[x]) for x in range(N))
    assert sites <= 3 * len(pieces) * lam1 + (2 * n + 1) * n, (sites, len(pieces), lam1, n)
    return CF, sites, len(pieces)

# ---------------------------------------------------------------- random many-charge covers
def random_cover(T, Gr, nroots, nedits, spread, rng, drag=0):
    n, mul, inv, e = Gr; N = T.N; E1, E2 = grid(T)
    if nroots == 0:
        h = [rng.randrange(n) for _ in range(N)]
        C = Conn(Gr, E1, E2, [mul[h[E1[x]]][inv[h[x]]] for x in range(N)], [mul[h[E2[x]]][inv[h[x]]] for x in range(N)])
    else:
        C = Conn(Gr, E1, E2, [rng.randrange(n) for _ in range(N)], [rng.randrange(n) for _ in range(N)])
        roots = rng.sample(range(N), nroots)
        par = {r: None for r in roots}; order = list(roots); i = 0
        while i < len(order):
            x = order[i]; i += 1
            for y in (E1[x], E2[x], C.ib[x], C.ic[x]):
                if y not in par: par[y] = x; order.append(y)
        for y in reversed(order):
            if par[y] is not None and y in C.charged(): C.push(y, par[y])
    centre = T.pt(rng.randrange(N))
    for _ in range(nedits):                               # each edit creates a neutral local dipole
        z = (centre[0] + rng.randint(-spread, spread), centre[1] + rng.randint(-spread, spread))
        ed = (rng.choice('bc'), T.idx(z)); C.set(ed, rng.randrange(n))
        if drag:                                          # drag one end of the new dipole a few steps away
            f = T.idx(z)
            for _ in range(rng.randint(0, drag)):
                st = rng.choice([(1, 0), (-1, 0), (0, 1), (0, -1)]); z2 = (z[0] + st[0], z[1] + st[1])
                if T.idx(z) in C.charged() and T.idx(z2) != T.idx(z): C.push(T.idx(z), T.idx(z2))
                z = z2
    return C

def main():
    name, seed, ncases = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    Nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 30
    nmax = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    Gr, act, regular = ygroup(name); m = len(act[0]); rng = random.Random(seed)
    stats = {'boxcount_checks': 0}; done = 0; tally = {}; worst = {}
    while done < ncases:
        shape = rng.choice(['thin', 'random', 'thick', 'thick'])
        if shape == 'thin': a = rng.randint(2, 4); d = rng.randint(6, max(6, Nmax // a))
        elif shape == 'random': a = rng.randint(3, Nmax); d = rng.randint(1, max(1, (2 * Nmax) // a))
        else: a = rng.randint(12, 22); d = rng.randint(12, 22)
        if a * d < 6: continue
        T = Torus((a, 0), (rng.randrange(a), d))
        w, k, v, u = T.frame(); lam1 = abs(w[0]) + abs(w[1])
        if lam1 < 2: continue
        if shape == 'thick': C0 = random_cover(T, Gr, 0, rng.randint(1, 3), rng.choice([1, 2, 6]), rng, rng.choice([0, 3, 5]))
        else: C0 = random_cover(T, Gr, rng.choice([0, 0, 1, 2, 3]), rng.randint(0, nmax), rng.choice([1, 2, 4, 8]), rng)
        Q = C0.charged(); n = len(Q)
        if n == 0: continue
        b, c = perms(C0, act)
        M = min(24, lam1 + 6)
        rl = rho_lower(b, c, M)
        outs = {}
        rB = construction_B(T, C0, act, lam1, b, c, stats)
        if rB is not None:
            theta, CB, sB, costB = rB; b2, c2 = perms(CB, act); assert np.array_equal(b2[c2], c2[b2])
            dB = max(rk(b2, b), rk(c2, c)); assert dB <= costB <= m * sB
            outs['B'] = dB
        if True:
            CA, sA, p = construction_A(T, C0, stats); b2, c2 = perms(CA, act); assert np.array_equal(b2[c2], c2[b2])
            dA = max(rk(b2, b), rk(c2, c)); assert dA <= m * sA
            outs['A'] = dA
        if not outs: continue
        dist = min(outs.values()); case = min(outs, key=outs.get)
        if regular: assert dist <= 10240 * rl ** 4 / m ** 3 + 1e-9, ('THEOREM A BOUND FAILS', dist, rl)
        assert dist <= 608 * rl ** 4 * (rl + m) + 1e-9, ('THEOREM B BOUND FAILS', dist, rl)
        assert 2 * comm_rank(b, c, 1, 1) >= sum(supp(act, C0.hol(q)) for q in Q)
        tally[case] = tally.get(case, 0) + 1
        worst[case] = max(worst.get(case, 0), dist / rl)
        done += 1
        print(name, 'N=%d a=%d c=%d d=%d lam1=%d n=%d' % (T.N, T.a, T.c, T.d, lam1, n),
              ' '.join('%s:%d' % kv for kv in sorted(outs.items())), 'theta=%s' % (rB[0] if rB else '-'),
              'rho>=%.3f dist/rho=%.3f' % (rl, dist / rl), flush=True)
    print('SUMMARY', name, 'cases', done, 'best construction', tally, 'box-count checks', stats['boxcount_checks'],
          'worst dist/rho_lower by construction', {k: round(x, 3) for k, x in worst.items()})

if __name__ == '__main__':
    main()
