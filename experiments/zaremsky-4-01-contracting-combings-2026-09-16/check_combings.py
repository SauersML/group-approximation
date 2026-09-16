#!/usr/bin/env python3
"""Finite-window checks for the 2026-09-16 contracting-combing notes.

Evidence only; the proofs are in
research/artifacts/zaremsky-4-01-contracting-combings-2026-09-16.md.

Alonso's contracting condition (Zaremsky arXiv:1812.10976v3, Section 6.1):
a combing s is contracting with constant C >= 2 if for all g, h and all
n' <= n with c = floor(C/2) <= n,
    d(s(g)(n), s(h)(n')) <= C  implies  d(s(g)(n - c), s(h)(n')) <= C.

Parts:
  1. the one-dimensional clamp inequality, exhaustively on a range;
  2. four groups acting transitively on Z^n by signed-permutation integral
     affine maps: the word metric of S = {g != 1 : |t_g|_inf <= 1} is computed
     by breadth-first search and compared with max(|t_g - t_h|_inf, 1); then
     the clamp combing is checked to be a combing and contracting on a window;
  3. the local obstruction for geodesic combings of Z^d with the standard
     generators: which backward vectors w survive in the orthant interior;
  4. a candidate geodesic combing of Z^2 (standard generators) with C = 4, 5.

Single-threaded; run with `timeout 600 python3 check_combings.py`.
"""
import itertools
import sys


def clamp(x, r):
    return max(-r, min(r, x))


def clampv(v, r):
    return tuple(clamp(x, r) for x in v)


def linf(u, v):
    return max((abs(a - b) for a, b in zip(u, v)), default=0)


# ---------------------------------------------------------------- part 1
def part1(R=14):
    bad = 0
    count = 0
    for C in range(2, 8):
        c = C // 2
        for r in range(c, R + 1):
            for rp in range(0, r + 1):
                for x in range(-R - 2, R + 3):
                    a = clamp(x, r)
                    a2 = clamp(x, r - c)
                    for y in range(-R - 2, R + 3):
                        b = clamp(y, rp)
                        count += 1
                        if abs(a - b) <= C and abs(a2 - b) > C:
                            bad += 1
    print(f"part1 clamp inequality: {count} cases, {bad} failures")
    return bad == 0


# ---------------------------------------------------------------- part 2
# An element is (A, t, f): A a signed permutation matrix stored as a tuple of
# rows, t in Z^n, f an element of a finite tag group Z/m acting trivially
# (used for the Z^n x F example).  Composition (A,t,f)(B,u,g) = (AB, t+Au, f+g).
def matmul(A, B):
    n = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n))
                 for i in range(n))


def matvec(A, v):
    return tuple(sum(A[i][k] * v[k] for k in range(len(v))) for i in range(len(v)))


def ident(n):
    return tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))


def signed_perms(n):
    out = []
    for p in itertools.permutations(range(n)):
        for s in itertools.product((1, -1), repeat=n):
            out.append(tuple(tuple(s[i] if j == p[i] else 0 for j in range(n))
                             for i in range(n)))
    return out


class Group:
    def __init__(self, name, n, m, elements_with_small_t):
        """elements_with_small_t: all (A, t, f) in G with |t|_inf <= 1."""
        self.name, self.n, self.m = name, n, m
        one = (ident(n), (0,) * n, 0)
        self.one = one
        self.S = [g for g in elements_with_small_t if g != one]

    def mul(self, g, h):
        A, t, f = g
        B, u, k = h
        return (matmul(A, B), tuple(a + b for a, b in zip(t, matvec(A, u))),
                (f + k) % self.m)

    def inv(self, g):
        A, t, f = g
        Ai = tuple(zip(*A))  # signed permutation: inverse is transpose
        return (Ai, tuple(-x for x in matvec(Ai, t)), (-f) % self.m)


def ball(G, L):
    """Breadth-first search: word lengths of all elements of length <= L."""
    dist = {G.one: 0}
    frontier = [G.one]
    for k in range(1, L + 1):
        nxt = []
        for g in frontier:
            for s in G.S:
                h = G.mul(g, s)
                if h not in dist:
                    dist[h] = k
                    nxt.append(h)
        frontier = nxt
    return dist


def check_group(G, L=6, R=3, Cs=(2, 3, 4, 5)):
    dist = ball(G, L)
    ok = True
    # (a) word metric formula on the ball: |g| = max(|t_g|_inf, 1) for g != 1
    for g, k in dist.items():
        want = 0 if g == G.one else max(max(abs(x) for x in g[1]), 1)
        if k != want:
            print(f"  metric mismatch {g}: bfs {k}, formula {want}")
            ok = False
            break
    # completeness inside the ball: every t with |t|_inf <= L - 1 and every
    # stabilizer coset appears; count elements with t = 0
    stab = [g for g in dist if all(x == 0 for x in g[1])]
    for t in itertools.product(range(-(L - 1), L), repeat=G.n):
        if not any(g[1] == t for g in dist):
            print(f"  translation {t} not reached")
            ok = False
            break
    # (b) clamp combing on the window |t|_inf <= R
    sigma = {}
    for g in sorted(dist, key=lambda x: (dist[x], repr(x))):
        sigma.setdefault(g[1], g)
    sigma[(0,) * G.n] = G.one
    window = [g for g in dist if max(abs(x) for x in g[1]) <= R]
    T = R + 1

    def comb(g, n):
        if n == 0:
            return G.one
        if n >= max(abs(x) for x in g[1]):
            return g
        return sigma[clampv(g[1], n)]

    idx = {g: i for i, g in enumerate(window)}
    invs = [G.inv(g) for g in window]
    D = [[dist[G.mul(invs[i], h)] for h in window] for i in range(len(window))]

    def d(g, h):
        return D[idx[g]][idx[h]]

    paths = {g: [comb(g, n) for n in range(T + 1)] for g in window}
    for g in window:
        for n in range(T):
            if d(paths[g][n], paths[g][n + 1]) > 1:
                print(f"  not a path at {g}, n={n}")
                ok = False
        if paths[g][T] != g:
            ok = False
    failures = 0
    checks = 0
    for C in Cs:
        c = C // 2
        for g in window:
            for h in window:
                for n in range(c, T + 1):
                    for n2 in range(0, n + 1):
                        checks += 1
                        if d(paths[g][n], paths[h][n2]) <= C and \
                                d(paths[g][n - c], paths[h][n2]) > C:
                            failures += 1
    print(f"part2 {G.name}: |S|={len(G.S)}, |Stab(0)|={len(stab)}, "
          f"ball elements={len(dist)}, window={len(window)}, "
          f"contracting checks={checks}, failures={failures}, metric ok={ok}")
    return ok and failures == 0


def groups():
    out = []
    unit = list(itertools.product((-1, 0, 1), repeat=2))
    # Z^2 with the l-infinity generators
    out.append(Group("Z^2 (l-inf)", 2, 1, [(ident(2), t, 0) for t in unit]))
    # Z^2 x Z/3, F acting trivially
    out.append(Group("Z^2 x Z/3", 2, 3,
                     [(ident(2), t, f) for t in unit for f in range(3)]))
    # Z^2 semidirect B_2 (all 8 signed permutations)
    out.append(Group("Z^2 x| B_2", 2, 1,
                     [(A, t, 0) for A in signed_perms(2) for t in unit]))
    # Klein bottle group: (m,k) acts by x -> diag((-1)^k,1) x + (m,k)
    def klein(m, k):
        return (((-1) ** (k % 2), 0), (0, 1)), (m, k), 0
    out.append(Group("Klein bottle", 2, 1,
                     [klein(m, k) for m, k in unit]))
    # screw 4_1 in scaled coordinates: (a,b,k) acts by x -> R^k x + (a,b,k)
    Rm = ((0, -1, 0), (1, 0, 0), (0, 0, 1))
    pows = [ident(3)]
    for _ in range(3):
        pows.append(matmul(Rm, pows[-1]))
    out.append(Group("screw 4_1 (scaled)", 3, 1,
                     [(pows[k % 4], (a, b, k), 0)
                      for a, b, k in itertools.product((-1, 0, 1), repeat=3)]))
    return out


# ---------------------------------------------------------------- part 3
def part3(dims=(2, 3, 4), Cs=range(2, 10)):
    """Interior obstruction: p deep in the positive orthant with |p|_1 = n,
    w >= 0 with |w|_1 = c (backward vector along a geodesic), q any point with
    |q|_1 <= n and |p - q|_1 <= C (q = s(q)(n) for a geodesic combing).  A
    vector w survives iff no q violates |p - w - q|_1 <= C."""
    for dim in dims:
        for C in Cs:
            c = C // 2
            p = tuple([C + 3] * dim)
            n = sum(p)
            survivors = []
            for w in itertools.product(range(c + 1), repeat=dim):
                if sum(w) != c:
                    continue
                pw = tuple(a - b for a, b in zip(p, w))
                violated = False
                for delta in itertools.product(range(-C, C + 1), repeat=dim):
                    if sum(abs(x) for x in delta) > C:
                        continue
                    q = tuple(a + b for a, b in zip(p, delta))
                    if sum(abs(x) for x in q) > n:
                        continue
                    if sum(abs(a - b) for a, b in zip(pw, q)) > C:
                        violated = True
                        break
                if not violated:
                    survivors.append(w)
            print(f"part3 Z^{dim} standard, C={C}: surviving backward vectors {survivors}")


# ---------------------------------------------------------------- part 4
def geodesic_path_z2(g):
    """Axis first, then staircase ending with (x-step, y-step) pairs, by
    octant symmetry.  Returns positions at times 0..|g|_1."""
    a, b = g
    sa, sb = (1 if a >= 0 else -1), (1 if b >= 0 else -1)
    A, B = abs(a), abs(b)
    pts = [(0, 0)]
    x = y = 0
    if A >= B:
        for _ in range(A - B):
            x += 1
            pts.append((x, y))
        for _ in range(B):
            x += 1
            pts.append((x, y))
            y += 1
            pts.append((x, y))
    else:
        for _ in range(B - A):
            y += 1
            pts.append((x, y))
        for _ in range(A):
            y += 1
            pts.append((x, y))
            x += 1
            pts.append((x, y))
    return [(sa * u, sb * v) for u, v in pts]


def part4(R=9, Cs=(4, 5)):
    pts = [g for g in itertools.product(range(-R, R + 1), repeat=2)]
    T = 2 * R + 1
    paths = {}
    for g in pts:
        pth = geodesic_path_z2(g)
        paths[g] = pth + [g] * (T + 1 - len(pth))

    def l1(u, v):
        return abs(u[0] - v[0]) + abs(u[1] - v[1])

    for C in Cs:
        c = C // 2
        failures = []
        checks = 0
        for g in pts:
            for h in pts:
                for n in range(c, T + 1):
                    p = paths[g][n]
                    p2 = paths[g][n - c]
                    for n2 in range(0, n + 1):
                        q = paths[h][n2]
                        checks += 1
                        if l1(p, q) <= C and l1(p2, q) > C:
                            if len(failures) < 3:
                                failures.append((g, n, h, n2))
                            else:
                                failures.append(None)
        nf = len(failures)
        print(f"part4 Z^2 standard, axis-then-staircase geodesic combing, C={C}, "
              f"window R={R}: checks={checks}, failures={nf}, "
              f"examples={[f for f in failures[:3]]}")


# ---------------------------------------------------------------- part 5
# Certificate generator for the l1-product obstruction on Z^2 with the
# standard generators.  For any combing (given as a path function) it walks
# the square g, g + C e_b, g + C e_a + C e_b, g + C e_a (a = last-step axis of
# g) and finds x, q with d(x, q) = C, d(s(x)(T(x) - 1), q) = C + 1 and
# T(q) <= T(x) + c - 1, which violates the contracting condition at
# (g, h, n, n') = (x, q, T(x) + c - 1, T(x) + c - 1).  The violation is then
# re-verified by direct evaluation.
def l1(u, v):
    return sum(abs(a - b) for a, b in zip(u, v))


def arrival(path_fn, g, tmax=10000):
    t = 0
    while path_fn(g, t) != g or any(path_fn(g, u) != g for u in range(t, t + 3)):
        t += 1
        if t > tmax:
            raise RuntimeError("no arrival")
    # smallest t with s(g)(u) = g for all u >= t (paths here are monotone in t)
    while t > 0 and path_fn(g, t - 1) == g:
        t -= 1
    return t


def certificate(path_fn, g, C):
    c = C // 2
    Tg = arrival(path_fn, g)
    last = path_fn(g, Tg - 1)
    a = 0 if last[0] != g[0] else 1
    b = 1 - a
    ea = (1, 0) if a == 0 else (0, 1)
    eb = (1, 0) if b == 0 else (0, 1)
    square = [g, (g[0] + C * eb[0], g[1] + C * eb[1]),
              (g[0] + C * (ea[0] + eb[0]), g[1] + C * (ea[1] + eb[1])),
              (g[0] + C * ea[0], g[1] + C * ea[1])]
    for x in square:
        Tx = arrival(path_fn, x)
        px = path_fn(x, Tx - 1)
        for q in square:
            if l1(x, q) != C or l1(px, q) != C + 1:
                continue
            if arrival(path_fn, q) <= Tx + c - 1:
                n = Tx + c - 1
                # direct re-verification of the violated implication
                hyp = l1(path_fn(x, n), path_fn(q, n)) <= C
                concl = l1(path_fn(x, n - c), path_fn(q, n)) <= C
                if hyp and not concl:
                    return (x, q, n, n)
    return None


def shortlex_z2(g, t):
    a, b = g
    sa, sb = (1 if a >= 0 else -1), (1 if b >= 0 else -1)
    A, B = abs(a), abs(b)
    x = min(t, A)
    y = min(max(t - A, 0), B)
    return (sa * x, sb * y)


def staircase_z2(g, t):
    pth = geodesic_path_z2(g)
    return pth[min(t, len(pth) - 1)]


def lazy_linf_z2(g, t):
    # emulate the l-infinity clamp with axis steps: odd times update x, even y
    r = t // 2
    if t % 2 == 1:
        return (clamp(g[0], r + 1), clamp(g[1], r))
    return (clamp(g[0], r), clamp(g[1], r))


def slow_shortlex_z2(g, t):
    return shortlex_z2(g, t // 3)


def part5(Cs=(2, 3, 4, 5, 6, 7)):
    ok = True
    for name, fn in [("shortlex", shortlex_z2), ("axis-then-staircase", staircase_z2),
                     ("lazy l-inf clamp", lazy_linf_z2), ("slow shortlex", slow_shortlex_z2)]:
        for C in Cs:
            for g in [(7, 3), (3, 7), (-5, 9), (8, -8), (0, 11)]:
                cert = certificate(fn, g, C)
                if cert is None:
                    print(f"part5 {name}, C={C}, g={g}: NO CERTIFICATE FOUND")
                    ok = False
                else:
                    x, q, n, n2 = cert
            print(f"part5 {name}, C={C}: violation certificates found for all test points; "
                  f"last: g={x}, h={q}, n=n'={n}")
    return ok


if __name__ == "__main__":
    all_ok = part1()
    for G in groups():
        all_ok = check_group(G, L=6 if G.n == 2 else 5, R=3 if G.n == 2 else 2) and all_ok
    part3()
    part4()
    all_ok = part5() and all_ok
    print("ALL POSITIVE CHECKS PASSED" if all_ok else "SOME POSITIVE CHECK FAILED")
    sys.exit(0 if all_ok else 1)
