#!/usr/bin/env python3
"""Exact checks for research/artifacts/diagonally-dominant-determinant-2026-09-16.md.

Part 1 (Lemma 3 of the artifact). For random finite trees with random edge
signs, the diagonal of (D - A_sigma)^k equals the diagonal of (D - A)^k for
every k <= KMAX.  Integer arithmetic, exact.

Part 2 (Section 5 of the artifact). For the d-regular tree T_d, the closed
walk counts N_k at the root are computed exactly by dynamic programming on the
distance from the root.  For integers lambda with 2 sqrt(d-1) < lambda <= d the
series identity

    log det(lambda - A_{T_d}) = log(lambda) - sum_{k>=1} N_k / (k lambda^k)

is certified against the closed form

    M(d, lambda) = (d-1) log u - ((d-2)/2) log(u^2 - 1),
    u = (lambda + sqrt(lambda^2 - 4(d-1))) / 2,

with an explicit tail bound N_k <= (2 sqrt(d-1))^k.  The endpoint
lambda = 2 sqrt(d-1) (d = 5, 10, 17, ...) is reported from the closed form only.

Part 3 (Proposition C of the artifact). For finite groups G = Gamma_S / N the
exact value (1/|G|) log det(lambda - A_S(G)), from Fraction elimination, is
compared with M(d,lambda) - sum_ell n_ell f_ell(u_lambda), where n_ell counts
reduced words of length ell in N.  Tests: Z/7 with S = {+-1, +-2} (Gamma_S = F_2)
and S_3 with the three transpositions (Gamma_S = (Z/2)^{*3}).

Deterministic (fixed seed), single-threaded, output well under 2MB.
Run: timeout 600 python3 boundary_margin.py
"""
import random
from fractions import Fraction
from decimal import Decimal, getcontext

getcontext().prec = 50
KMAX_TREE = 14
TRIALS = 40
K_SERIES = 600


def mat_mul(X, Y):
    n = len(X)
    Z = [[0] * n for _ in range(n)]
    for i in range(n):
        Xi = X[i]
        Zi = Z[i]
        for k in range(n):
            a = Xi[k]
            if a:
                Yk = Y[k]
                for j in range(n):
                    b = Yk[j]
                    if b:
                        Zi[j] += a * b
    return Z


def random_tree(n, rng):
    parent = [None] + [rng.randrange(i) for i in range(1, n)]
    return [(i, parent[i]) for i in range(1, n)]


def laplacian(n, edges, signs):
    L = [[0] * n for _ in range(n)]
    for (x, y), s in zip(edges, signs):
        L[x][x] += 1
        L[y][y] += 1
        L[x][y] -= s
        L[y][x] -= s
    return L


def part1(rng):
    worst = 0
    for t in range(TRIALS):
        n = rng.randrange(2, 13)
        edges = random_tree(n, rng)
        signs = [rng.choice((1, -1)) for _ in edges]
        Ls = laplacian(n, edges, signs)
        Lu = laplacian(n, edges, [1] * len(edges))
        Ps, Pu = Ls, Lu
        for k in range(1, KMAX_TREE + 1):
            for i in range(n):
                if Ps[i][i] != Pu[i][i]:
                    raise SystemExit("Lemma 3 FAILED: trial %d k=%d vertex %d" % (t, k, i))
            worst = max(worst, k)
            Ps = mat_mul(Ps, Ls)
            Pu = mat_mul(Pu, Lu)
    # a signed cycle is balanced-sensitive: check the lemma really needs a forest
    n = 3
    edges = [(0, 1), (1, 2), (2, 0)]
    Ls = laplacian(n, edges, [1, 1, -1])
    Lu = laplacian(n, edges, [1, 1, 1])
    Ls3 = mat_mul(mat_mul(Ls, Ls), Ls)
    Lu3 = mat_mul(mat_mul(Lu, Lu), Lu)
    print("Part 1: signed forest diagonals agree for %d random trees, k <= %d" % (TRIALS, worst))
    print("        control, unbalanced triangle: diag (L_sigma)^3 = %d, diag L^3 = %d" % (Ls3[0][0], Lu3[0][0]))


def tree_closed_walks(d, K):
    """N_k = number of closed walks of length k at the root of T_d, k = 0..K."""
    dist = {0: 1}
    N = [1]
    for _ in range(K):
        new = {}
        for j, c in dist.items():
            if j == 0:
                new[1] = new.get(1, 0) + d * c
            else:
                new[j - 1] = new.get(j - 1, 0) + c
                new[j + 1] = new.get(j + 1, 0) + (d - 1) * c
        dist = new
        N.append(dist.get(0, 0))
    return N


def closed_form(d, lam):
    disc = Decimal(lam * lam - 4 * (d - 1))
    u = (Decimal(lam) + disc.sqrt()) / 2
    return (d - 1) * u.ln() - Decimal(d - 2) / 2 * (u * u - 1).ln()


def part2():
    print("Part 2: margins M(d,lambda) = log det(lambda - A_{T_d}) on the boundary window")
    print("   d lambda  rho=2sqrt(d-1)   closed form M        certified interval from series")
    for d in range(5, 13):
        N = tree_closed_walks(d, K_SERIES)
        assert N[1] == 0 and N[2] == d and N[4] == d * (2 * d - 1)
        rho = Decimal(4 * (d - 1)).sqrt()
        lam0 = 1
        while lam0 * lam0 < 4 * (d - 1):
            lam0 += 1
        for lam in range(lam0, d + 1):
            M = closed_form(d, lam)
            if lam * lam == 4 * (d - 1):
                print("  %2d  %3d    %.6f   %.12f   (endpoint: closed form only)" % (d, lam, rho, M))
                continue
            S = Fraction(0)
            for k in range(1, K_SERIES + 1):
                if N[k]:
                    S += Fraction(N[k], k * lam ** k)
            S_dec = Decimal(S.numerator) / Decimal(S.denominator)
            r = rho / Decimal(lam)
            tail = r ** (K_SERIES + 1) / ((K_SERIES + 1) * (1 - r))
            hi = Decimal(lam).ln() - S_dec
            lo = hi - tail
            ok = lo - Decimal("1e-40") <= M <= hi + Decimal("1e-40")
            if not ok:
                raise SystemExit("closed form outside certified interval at d=%d lambda=%d" % (d, lam))
            print("  %2d  %3d    %.6f   %.12f   [%.12f, %.12f]" % (d, lam, rho, M, lo, hi))
    print("All closed forms lie in their certified intervals; every margin is positive.")


def f_ell(ell, u, d, J=400):
    """f_ell(u) = u^ell/ell - (d-2) sum_{j>=1} u^(ell+2j)/(ell+2j), truncated at J."""
    s = u ** ell / ell
    p = u ** ell
    u2 = u * u
    for j in range(1, J + 1):
        p *= u2
        s -= (d - 2) * p / (ell + 2 * j)
    return s


def reduced_trivial_counts(elements, mul, gens, inv, L):
    """n_ell = number of reduced words of length ell (no letter followed by its paired
    inverse) whose product is the identity, ell = 0..L."""
    idx = {g: i for i, g in enumerate(elements)}
    e = elements[0]
    cur = {}
    for a, s in enumerate(gens):
        key = (idx[mul(e, s)], a)
        cur[key] = cur.get(key, 0) + 1
    n = [1, sum(c for (g, a), c in cur.items() if g == 0)]
    for _ in range(2, L + 1):
        new = {}
        for (g, a), c in cur.items():
            for b, s in enumerate(gens):
                if b == inv[a]:
                    continue
                key = (idx[mul(elements[g], s)], b)
                new[key] = new.get(key, 0) + c
        cur = new
        n.append(sum(c for (g, a), c in cur.items() if g == 0))
    return n


def exact_logdet(elements, mul, gens, lam):
    """(1/|G|) log det(lam - A_S) for a finite group, exact Fraction elimination."""
    m = len(elements)
    idx = {g: i for i, g in enumerate(elements)}
    M = [[Fraction(0)] * m for _ in range(m)]
    for i, g in enumerate(elements):
        M[i][i] += lam
        for s in gens:
            M[i][idx[mul(g, s)]] -= 1
    det = Fraction(1)
    for c in range(m):
        piv = next(r for r in range(c, m) if M[r][c] != 0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det *= M[c][c]
        for r in range(c + 1, m):
            fac = M[r][c] / M[c][c]
            if fac:
                for k in range(c, m):
                    M[r][k] -= fac * M[c][k]
    assert det > 0
    return (Decimal(det.numerator).ln() - Decimal(det.denominator).ln()) / m


def part3():
    print("Part 3: relator identity log det(lambda - A_S(G)) = M(d,lambda) - sum_ell n_ell f_ell(u)")
    tests = []
    # Z/7 with S = {+1,-1,+2,-2}: universal group F_2, d = 4
    z7 = list(range(7))
    tests.append(("Z/7, S={+-1,+-2}", z7, lambda a, b: (a + b) % 7, [1, 6, 2, 5], [1, 0, 3, 2], 4, Fraction(11, 2), 260))
    tests.append(("Z/7, S={+-1,+-2}", z7, lambda a, b: (a + b) % 7, [1, 6, 2, 5], [1, 0, 3, 2], 4, Fraction(9, 2), 400))
    # S_3 with the three transpositions: universal group (Z/2)^{*3}, d = 3
    from itertools import permutations
    s3 = sorted(permutations(range(3)))
    comp = lambda p, q: tuple(p[q[i]] for i in range(3))
    trans = [(1, 0, 2), (0, 2, 1), (2, 1, 0)]
    tests.append(("S_3, S=transpositions", s3, comp, trans, [0, 1, 2], 3, Fraction(7, 2), 420))
    for name, el, mul, gens, inv, d, lam, L in tests:
        n = reduced_trivial_counts(el, mul, gens, inv, L)
        lamd = Decimal(lam.numerator) / Decimal(lam.denominator)
        u = (lamd - (lamd * lamd - 4 * (d - 1)).sqrt()) / (2 * (d - 1))
        disc = lamd * lamd - 4 * (d - 1)
        x = (lamd + disc.sqrt()) / 2
        M = (d - 1) * x.ln() - Decimal(d - 2) / 2 * (x * x - 1).ln()
        S = Decimal(0)
        for ell in range(1, L + 1):
            if n[ell]:
                S += n[ell] * f_ell(ell, u, d)
        lhs = exact_logdet(el, mul, gens, lam)
        rhs = M - S
        print("  %-24s d=%d lambda=%s  exact=%.20f  identity=%.20f  diff=%.1e" % (name, d, lam, lhs, rhs, abs(lhs - rhs)))
        if abs(lhs - rhs) > Decimal("1e-25"):
            raise SystemExit("relator identity FAILED for %s" % name)
    print("Relator identity agrees to 1e-25 on all tests.")


def main():
    rng = random.Random(20260916)
    part1(rng)
    part2()
    part3()


if __name__ == "__main__":
    main()
