#!/usr/bin/env python3
"""Flat-rate point versus l2 point on free products of Z/2's and Z/3's.

Group: Gamma = (Z/2)^{*k} * (Z/3)^{*m}, generating set = the involutions x_i
and r_j, r_j^{-1}; simple random walk, degree d = k + 2m.  The Cayley graph is
a block graph: K_2 blocks (one per x_i-coset) and K_3 blocks (one per
<r_j>-coset).

Computed quantities
  R = 1/rho              radius of convergence of the Green function
  a(R), F(R)             first-passage generating functions e -> x_i, e -> r_j
  p_c    : sum_x tau_p(o,x)              diverges   (Phi(p,2q) = 1)
  p_2    : sum_x tau_p(o,x)^2            diverges   (Phi(p^2,2q^2) = 1)
  p_G    : sum_x G_R(o,x) tau_p(o,x)     diverges   (Phi(a p, 2 F q) = 1)
where q = p + (1-p) p^2 is the K_3 two-point function and
Phi(u2,u3) = k u2/(1+u2) + m u3/(1+u3) is the free-product sum criterion.

Theorem used (research/artifacts/fpbs-free-product-flat-rate-2026-09-18.md):
sum_n a_n(p) z^n = sum_x G_z(o,x) tau_p(o,x) with a_n(p) = E tau_p(o,X_n), so
lambda(p) = rho iff this series converges for every z < R, which on these free
products holds iff Phi(a(R)p, 2F(R)q(p)) <= 1.  Hence the flat-rate point is
p_* = p_G exactly.  The strict inequality p_G > p_2 is proved by a convexity
argument; this script only gives the numerical size of the gap, and the
certificate that the argument applies is certify_a_ne_b.py.  The numbers
below are floating point and are not certified.

Run:  python3 free_product_thresholds.py
"""
import itertools
import sys
from fractions import Fraction


def fp_map(a, F, z, k, m):
    d = k + 2 * m
    al = z / d
    Pa = al * (1 + ((k - 1) * a + 2 * m * F) * a)
    PF = al * (1 + F + (k * a + 2 * (m - 1) * F) * F)
    return Pa, PF


def jac(a, F, z, k, m):
    d = k + 2 * m
    al = z / d
    return (al * (2 * (k - 1) * a + 2 * m * F), al * (2 * m * a),
            al * (k * F), al * (1 + k * a + 4 * (m - 1) * F))


def minimal_solution(z, k, m, iters=200000, tol=1e-15):
    a = F = 0.0
    for _ in range(iters):
        na, nF = fp_map(a, F, z, k, m)
        if na > 50 or nF > 50:
            return None
        if abs(na - a) + abs(nF - F) < tol:
            return na, nF
        a, F = na, nF
    return a, F


def branch_point(k, m):
    """Newton on (a,F,z): fixed point plus det(I-J)=0."""
    # start from bisection estimate
    lo, hi = 1.0, 2.0
    for _ in range(60):
        mid = (lo + hi) / 2
        s = minimal_solution(mid, k, m, iters=20000, tol=1e-13)
        # a solution that is still moving counts as divergent
        if s is None:
            hi = mid
        else:
            na, nF = fp_map(s[0], s[1], mid, k, m)
            if abs(na - s[0]) + abs(nF - s[1]) > 1e-9:
                hi = mid
            else:
                lo = mid
    z = lo
    a, F = minimal_solution(z, k, m)
    for _ in range(100):
        Pa, PF = fp_map(a, F, z, k, m)
        j11, j12, j21, j22 = jac(a, F, z, k, m)
        g1, g2 = Pa - a, PF - F
        g3 = (1 - j11) * (1 - j22) - j12 * j21
        # numerical Jacobian of (g1,g2,g3)
        h = 1e-9
        def G(v):
            aa, FF, zz = v
            Pa_, PF_ = fp_map(aa, FF, zz, k, m)
            q11, q12, q21, q22 = jac(aa, FF, zz, k, m)
            return (Pa_ - aa, PF_ - FF, (1 - q11) * (1 - q22) - q12 * q21)
        v = [a, F, z]
        g = G(v)
        M = []
        for i in range(3):
            w = list(v)
            w[i] += h
            gw = G(w)
            M.append([(gw[r] - g[r]) / h for r in range(3)])
        # M[i][r] = d g_r / d v_i ; solve sum_i M[i][r] dv_i = -g_r
        A = [[M[i][r] for i in range(3)] for r in range(3)]
        dv = solve3(A, [-x for x in g])
        a, F, z = a + dv[0], F + dv[1], z + dv[2]
        if max(abs(x) for x in dv) < 1e-15:
            break
    return z, a, F


def solve3(A, b):
    import copy
    A = copy.deepcopy(A)
    b = list(b)
    n = 3
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(A[r][c]))
        A[c], A[p] = A[p], A[c]
        b[c], b[p] = b[p], b[c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            for cc in range(c, n):
                A[r][cc] -= f * A[c][cc]
            b[r] -= f * b[c]
    x = [0.0] * n
    for r in reversed(range(n)):
        x[r] = (b[r] - sum(A[r][cc] * x[cc] for cc in range(r + 1, n))) / A[r][r]
    return x


def Phi(u2, u3, k, m):
    return k * u2 / (1 + u2) + m * u3 / (1 + u3)


def q3(p):
    return p + (1 - p) * p * p


def root(f, lo=1e-9, hi=1 - 1e-12):
    flo, fhi = f(lo), f(hi)
    assert flo < 0 < fhi, (flo, fhi)
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


# ---------- independent brute-force check of the first-passage system ----------

def brute_return_probs(k, m, N):
    """Exact P^n(e,e), n<=N, by enumerating reduced words (exact rationals)."""
    gens = []  # (factor index, element) ; Z/2 factor elements {1}, Z/3 {1,2}
    for i in range(k):
        gens.append((i, 1, 2))
    for j in range(m):
        gens.append((k + j, 1, 3))
        gens.append((k + j, 2, 3))
    d = len(gens)

    def mult(word, g):
        f, e, order = g
        if word and word[-1][0] == f:
            ne = (word[-1][1] + e) % order
            return word[:-1] if ne == 0 else word[:-1] + ((f, ne),)
        return word + ((f, e),)

    dist = {(): Fraction(1)}
    out = [Fraction(1)]
    for n in range(1, N + 1):
        nd = {}
        for w, pr in dist.items():
            if len(w) > N - n + 1:
                continue  # cannot return in time
            for g in gens:
                w2 = mult(w, g)
                nd[w2] = nd.get(w2, 0) + pr / d
        dist = nd
        out.append(dist.get((), Fraction(0)))
    return out


def series_return_probs(k, m, N):
    """P^n(e,e) from the first-passage system as power series in z."""
    d = k + 2 * m
    # power series as lists of Fractions, truncated at N
    def mul(A, B):
        C = [Fraction(0)] * (N + 1)
        for i, x in enumerate(A):
            if x == 0:
                continue
            for j in range(N + 1 - i):
                C[i + j] += x * B[j]
        return C

    def add(*Ls):
        C = [Fraction(0)] * (N + 1)
        for L in Ls:
            for i in range(N + 1):
                C[i] += L[i]
        return C

    def scal(c, A):
        return [c * x for x in A]

    zser = [Fraction(0)] * (N + 1)
    zser[1] = Fraction(1, d)  # alpha = z/d
    one = [Fraction(1)] + [Fraction(0)] * N
    a = [Fraction(0)] * (N + 1)
    F = [Fraction(0)] * (N + 1)
    for _ in range(N + 2):
        inner_a = add(one, mul(add(scal(k - 1, a), scal(2 * m, F)), a))
        inner_F = add(one, F, mul(add(scal(k, a), scal(2 * (m - 1), F)), F))
        a, F = mul(zser, inner_a), mul(zser, inner_F)
    E = mul(zser, add(scal(k, a), scal(2 * m, F)))
    # G = 1/(1-E)
    Gs = [Fraction(0)] * (N + 1)
    Gs[0] = Fraction(1)
    for n in range(1, N + 1):
        Gs[n] = sum(E[i] * Gs[n - i] for i in range(1, n + 1))
    return Gs


def main():
    cases = [(2, 1), (1, 1), (3, 1), (1, 2), (2, 2), (4, 1)]
    print("check: brute-force P^n(e,e) vs first-passage system")
    for k, m in [(2, 1), (1, 2)]:
        N = 12
        b = brute_return_probs(k, m, N)
        s = series_return_probs(k, m, N)
        ok = all(b[n] == s[n] for n in range(N + 1))
        print(f"  k={k} m={m}: exact agreement up to n={N}: {ok}")
        if not ok:
            sys.exit(1)
    print()
    print(" k  m  deg   rho        a(R)       F(R)       p_c        p_2        p_G        p_G-p_2     Phi(A)       resid")
    rows = []
    for k, m in cases:
        z, a, F = branch_point(k, m)
        d = k + 2 * m
        # sanity: Green function finite at R
        E = (z / d) * (k * a + 2 * m * F)
        assert E < 1
        pc = root(lambda p: Phi(p, 2 * q3(p), k, m) - 1)
        p2 = root(lambda p: Phi(p * p, 2 * q3(p) ** 2, k, m) - 1)
        pG = root(lambda p: Phi(a * p, 2 * F * q3(p), k, m) - 1)
        rows.append((k, m, d, 1 / z, a, F, pc, p2, pG))
        # Phi(A): the Green l2 point; <= 1 always, = 1 when G'(R) is infinite
        phiA = Phi(a * a, 2 * F * F, k, m)
        Pa, PF = fp_map(a, F, z, k, m)
        resid = abs(Pa - a) + abs(PF - F)
        print(f" {k}  {m}  {d:3d}  {1/z:.8f} {a:.8f} {F:.8f} {pc:.8f} {p2:.8f} {pG:.8f} {pG-p2:+.3e}  {phiA:.10f} {resid:.1e}")
    # consistency check below z=1: G(z) * (1 + S(z)) = 1/(1-z)
    print()
    print("check: G(z)(1+S(z)) = 1/(1-z) for z<1 (S = sum over nontrivial x of F(o,x))")
    for k, m in cases[:2]:
        for zz in (0.5, 0.9):
            aa, FF = minimal_solution(zz, k, m)
            d = k + 2 * m
            E = (zz / d) * (k * aa + 2 * m * FF)
            Gz = 1 / (1 - E)
            th = Phi(aa, 2 * FF, k, m)
            S = th / (1 - th)
            print(f"  k={k} m={m} z={zz}: G(1+S)={Gz*(1+S):.12f}  1/(1-z)={1/(1-zz):.12f}")
    return rows


if __name__ == "__main__":
    main()
