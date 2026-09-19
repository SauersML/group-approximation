#!/usr/bin/env python3
"""Checks for thompson-f-product-forest-sets-have-density-at-most-3-5 (exact where stated).

Part A (exact, Fractions + exact PL arithmetic).  For random product indicator families
(cal A_s, cal B_s subsets of the trees with s leaves) and n <= NMAX, build
    Y_n = { E(T_0..T_{m-1}; i) : T_i in cal B, T_j in cal A for j != i }
and compute its density  <1_Y, K 1_Y> / |Y|  by brute force in the Cayley graph of
G = <s_0, s_1> (every one of the four neighbours x o g, g in {s_0^+-1, s_1^+-1}, is tested
for membership in Y).  Compare with the counting formula of route step 1,
    2 (sum_{s,t} X_s X_t Y_{n-s-t} + sum_m E_m Y_{n-m}) / sum_s B_s Y_{n-s}.

Part B (exact bisection).  The depth-<=k family cal A = cal B = D_k: R_k solving D_k(R) = 1
and the limit density 4 - 2 R_k; cross-check of V against the general limit formula
V = 2((sum X_s R^s)^2 + sum E_m R^m) / Q with the exact size counts of D_k.

Part C (float sanity only).  Random nu, eta: Psi = max_u S(u)^2 + sum min(nu, nu*eta) never
exceeds 3/2 + a^2 < 7/4, a = F(t-1), t the least integer with F(t) >= 1/2.
"""
import random
import sys
from fractions import Fraction as Fr
from collections import deque

sys.path.insert(0, '../thompson-f-norm-ansatz-2026-09-17')
sys.path.insert(0, '../thompson-f-cogrowth-2026-09-17')
from model_check import s0, s1, ident, moves  # noqa: E402

GENS = [s0, s0.inv(), s1, s1.inv()]
_TREES = {1: [()]}


def trees(s):
    if s not in _TREES:
        _TREES[s] = [(L, R) for k in range(1, s) for L in trees(k) for R in trees(s - k)]
    return _TREES[s]


def size(T):
    return 1 if T == () else size(T[0]) + size(T[1])


def depth(T):
    return 0 if T == () else 1 + max(depth(T[0]), depth(T[1]))


def forests(n):
    if n == 0:
        yield ()
        return
    for s in range(1, n + 1):
        for T in trees(s):
            for rest in forests(n - s):
                yield (T,) + rest


def elements(n):
    states = {(f, i) for f in forests(n) for i in range(len(f))}
    base = (tuple(() for _ in range(n)), 0)
    elem = {base: ident}
    dq = deque([base])
    while dq:
        x = dq.popleft()
        for g, y in moves(x):
            if y not in elem:
                elem[y] = g.then(elem[x])
                dq.append(y)
    assert len(elem) == len(states)
    return elem


def brute_density(elem, inA, inB):
    Y = [x for x in elem if inB(x[0][x[1]]) and all(inA(T) for j, T in enumerate(x[0]) if j != x[1])]
    keys = {elem[x].key() for x in Y}
    assert len(keys) == len(Y)
    deg = sum(1 for x in Y for g in GENS if g.then(elem[x]).key() in keys)
    return Fr(deg, len(Y)) if Y else None, len(Y)


def formula_density(n, inA, inB):
    a = {s: sum(1 for T in trees(s) if inA(T)) for s in range(1, n + 1)}
    b = {s: sum(1 for T in trees(s) if inB(T)) for s in range(1, n + 1)}
    x = {s: sum(1 for T in trees(s) if inA(T) and inB(T)) for s in range(1, n + 1)}
    e = {m: sum(1 for T in trees(m) if T != () and inB(T) and inB(T[0]) and inA(T[1]))
         for m in range(1, n + 1)}
    W = [1] + [0] * n
    for l in range(1, n + 1):
        W[l] = sum(a[s] * W[l - s] for s in range(1, l + 1))
    Yc = [sum(W[l] * W[k - l] for l in range(k + 1)) for k in range(n + 1)]
    D = sum(b[s] * Yc[n - s] for s in range(1, n + 1))
    sh = sum(x[s] * x[t] * Yc[n - s - t] for s in range(1, n + 1) for t in range(1, n + 1 - s))
    me = sum(e[m] * Yc[n - m] for m in range(2, n + 1))
    return (Fr(2 * (sh + me), D) if D else None), D


def part_a(NMAX=7, fam=40, seed=7):
    rng = random.Random(seed)
    allT = [T for s in range(1, NMAX + 1) for T in trees(s)]
    els = {n: elements(n) for n in range(1, NMAX + 1)}
    count = 0
    for f in range(fam):
        pa, pb = rng.choice([0.5, 0.8, 1.0]), rng.choice([0.3, 0.6, 0.9])
        SA = {T for T in allT if rng.random() < pa}
        SB = {T for T in allT if rng.random() < pb}
        if f % 4 == 0:
            SA.add(())  # leaf in cal A for some families
        k = rng.randint(1, 3)
        if f % 5 == 1:  # depth family
            SA = SB = {T for T in allT if depth(T) <= k}
        inA, inB = (lambda T: T in SA), (lambda T: T in SB)
        for n in range(1, NMAX + 1):
            d1, sz = brute_density(els[n], inA, inB)
            d2, D = formula_density(n, inA, inB)
            assert sz == D, (f, n, sz, D)
            assert d1 == d2, (f, n, d1, d2)
            count += 1
    return count


def depth_poly(k, smax):
    """coefficients c[s] = number of trees with s leaves and depth <= k, s <= smax"""
    c = [0] * (smax + 1)
    c[1] = 1
    for _ in range(k):
        sq = [0] * (smax + 1)
        for i in range(smax + 1):
            if c[i]:
                for j in range(smax + 1 - i):
                    sq[i + j] += c[i] * c[j]
        c = [0, 1] + sq[2:]
    return c


def Dk(k, x):
    d = x
    for _ in range(k):
        d = x + d * d
    return d


def part_b(KMAX=14, bits=80):
    rows = []
    for k in range(1, KMAX + 1):
        lo, hi = Fr(1, 4), Fr(1)
        assert Dk(k, lo) < 1 <= Dk(k, hi)
        for _ in range(bits):
            mid = (lo + hi) / 2
            if Dk(k, mid) < 1:
                lo = mid
            else:
                hi = mid
        R = hi
        rows.append((k, R, 4 - 2 * R))
        if k <= 5:  # general formula with exact counts; X = A = B, E_m = B_m (m >= 2), Q = 1
            N = 2 ** k
            c = depth_poly(k, N)
            assert sum(c) == sum(1 for s in range(1, N + 1) for T in trees(s) if depth(T) <= k) if k <= 3 else True
            E = sum(c[s] * R ** s for s in range(1, N + 1))
            assert abs(E - 1) < Fr(1, 2 ** (bits - 10))
            V = 2 * (E ** 2 + (E - c[1] * R)) / E
            assert abs(V - (4 - 2 * R)) < Fr(1, 2 ** (bits - 12))
    for i in range(1, len(rows)):
        assert rows[i][1] <= rows[i - 1][1] and rows[i][1] > Fr(1, 4)
    return rows


def psi(nu, eta):
    M = len(nu)
    conv = [0.0] * (2 * M + 2)
    for i in range(M):
        for j in range(M):
            conv[i + j + 2] += nu[i] * eta[j]
    Mterm = sum(min(nu[m - 1], conv[m]) for m in range(1, M + 1))
    best = 0.0
    for s in range(M):
        if eta[s] > 0 and nu[s] > 0:
            u = (nu[s] / eta[s]) ** 0.5
            best = max(best, sum(min(u * eta[r], nu[r] / u) for r in range(M)))
    return best ** 2 + Mterm


def part_c(trials=3000, seed=3):
    rng = random.Random(seed)
    worst = 0.0
    for _ in range(trials):
        M = rng.randint(1, 30)
        nu = [rng.random() ** rng.choice([1, 3, 8]) for _ in range(M)]
        eta = [rng.random() ** rng.choice([1, 3, 8]) for _ in range(M)]
        if rng.random() < 0.3:
            eta = list(nu)
        sn, se = sum(nu), sum(eta)
        nu = [v / sn for v in nu]
        eta = [v / se for v in eta]
        F, t = 0.0, 0
        while F < 0.5:
            t += 1
            F += nu[t - 1]
        a = sum(nu[: t - 1])
        p = psi(nu, eta)
        assert p <= 1.5 + a * a + 1e-12 and p < 1.75, (p, a)
        worst = max(worst, p)
    return worst


if __name__ == '__main__':
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    print('Part A: brute-force Cayley density == counting formula for %d (family, n) pairs, n <= %d'
          % (part_a(NMAX), NMAX))
    print('Part B: depth-<=k family, R_k decreasing and > 1/4, limit density 4 - 2R_k:')
    for k, R, d in part_b():
        print('  k=%2d  R_k=%.12f  density limit=%.12f' % (k, float(R), float(d)))
    print('Part C (float): max Psi over random pairs = %.6f  (all <= 3/2 + a^2 < 7/4)' % part_c())
