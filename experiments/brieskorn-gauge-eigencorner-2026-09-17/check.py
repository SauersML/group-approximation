#!/usr/bin/env python3
"""Gauge-field corona pairs for the Brieskorn lattice pi_1 Sigma(3,4,5).

Companion to research/brieskorn-345-gauge-pair-has-no-eigencorner.md.

For primes p with p = +-1 mod 8 and p = +-1 mod 5, G = PSL_2(F_p) is a
quotient of the (3,4,5) triangle group Delta = <a, b | a^4, b^3, (ba)^5>.
We find alpha, beta in G of orders 4, 3 with beta*alpha of order 5 that
generate G, and check:

  1. orders and generation (BFS), and the word metric for {alpha^+-1, beta^+-1};
  2. ker F^T is one-dimensional, spanned by (+1 on a- and b-faces, -1 on
     P-faces), by an exact union-find-with-parity computation;
  3. the gauge phases theta solving F theta = c' exist (least squares
     residual), and the relation defects of X = M_a L(alpha), Y = M_b L(beta)
         ||X^4 - Y^3||,  ||(YX)^5 - X^12||,  ||X^4 - D||,   D = diag(e^{i phi})
     are below the bounds 3pi/R + 2eps, 18pi/R + 4eps, 2pi/R + eps of the proof,
     where eps = 60 pi / (47 N).  These bounds tend to 0 as R -> infinity,
     but the P-defect bound 18 pi / R is below 2 only for R > 9 pi, beyond
     the diameters (<= 19) of the groups computable here.  So the numerics
     check the exact linear algebra and the bounds, not the smallness of
     ||(YX)^5 - X^12||, which is a proof-level asymptotic;
  4. ||X^4 - 1|| is close to 2 and tau(|D - 1|^2) is small;
  5. the spectral gap: lambda_2 of the Markov operator, and the Kazhdan lower
     bound kappa >= sqrt(2 (1 - lambda_2)) for {alpha^+-1, beta^+-1};
  6. the Thompson relator [beta alpha beta, alpha^2 beta alpha beta alpha^2]
     is NOT trivial in G, so the gauge unitaries are at distance >= 1 from
     satisfying it (zero diagonal), i.e. these models do not descend to T-bar;
  7. the scalar-phase ansatz X = D^a alpha, Y = D^b beta of the K(3,4) pair
     cannot satisfy the Brieskorn relation: 4a = 3b = m forces
     5(a + b) = 35 m / 12 != 3 m.

Deterministic (fixed seeds).  Run: python3 check.py
"""
import math
import random
import sys
from fractions import Fraction

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import lsqr, eigsh


def sqrt_mod(n, p):
    n %= p
    for x in range(p):
        if x * x % p == n:
            return x
    return None


def norm_elt(m, p):
    a, b, c, d = (x % p for x in m)
    lead = a if a else b
    if lead > (p - 1) // 2:
        a, b, c, d = (-a) % p, (-b) % p, (-c) % p, (-d) % p
    return (a, b, c, d)


def mul(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return norm_elt((a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h), p)


def inv(x, p):
    a, b, c, d = x
    return norm_elt((d, -b, -c, a), p)


def order(x, p):
    one = norm_elt((1, 0, 0, 1), p)
    y, k = x, 1
    while y != one:
        y = mul(y, x, p)
        k += 1
    return k


def find_triple(p, seed):
    """alpha of order 4, beta of order 3, beta*alpha of order 5, generating PSL_2(p)."""
    s = sqrt_mod(2, p)
    alpha = norm_elt((s, -1, 1, 0), p)
    rng = random.Random(seed)
    target = p * (p * p - 1) // 2
    while True:
        x = rng.randrange(p)
        y = rng.randrange(1, p)
        w = (1 - x) % p
        z = (x * w - 1) * pow(y, p - 2, p) % p
        beta = norm_elt((x, y, z, w), p)
        ba = mul(beta, alpha, p)
        if order(alpha, p) != 4 or order(beta, p) != 3 or order(ba, p) != 5:
            continue
        elts, dist = bfs(alpha, beta, p)
        if len(elts) == target:
            return alpha, beta, elts, dist


def bfs(alpha, beta, p):
    gens = [alpha, inv(alpha, p), beta, inv(beta, p)]
    one = norm_elt((1, 0, 0, 1), p)
    dist = {one: 0}
    elts = [one]
    i = 0
    while i < len(elts):
        g = elts[i]
        i += 1
        for s in gens:
            h = mul(s, g, p)
            if h not in dist:
                dist[h] = dist[g] + 1
                elts.append(h)
    return elts, dist


def orbits(perm):
    n = len(perm)
    oid = -np.ones(n, dtype=np.int64)
    reps = []
    for g in range(n):
        if oid[g] < 0:
            k = len(reps)
            reps.append(g)
            h = g
            while oid[h] < 0:
                oid[h] = k
                h = perm[h]
    return oid, reps


def kernel_dim_FT(ia, ib, oa, ob, oP, na, nb, nP):
    """dim ker F^T by union-find with parity on the faces.

    Equations: x_a(oa[g]) + x_P(oP[g]) = 0 for each a-edge g, and
    x_b(ob[h]) + x_P(oP[alpha^-1 h]) = 0 for each b-edge h.  Every face gets
    a value forced up to sign by its component; a component contributes one
    dimension iff its parities are consistent."""
    n_f = na + nb + nP
    parent = list(range(n_f))
    par = [0] * n_f  # parity to parent

    def find(u):
        path = []
        while parent[u] != u:
            path.append(u)
            u = parent[u]
        root = u
        # compress
        acc = 0
        for v in reversed(path):
            acc ^= par[v]
            par[v] = acc
            parent[v] = root
        return root

    def parity(u):
        find(u)
        return par[u] if parent[u] != u else 0

    bad = set()

    def union(u, v, odd):
        ru, rv = find(u), find(v)
        pu, pv = parity(u), parity(v)
        if ru == rv:
            if (pu ^ pv) != odd:
                bad.add(ru)
            return
        parent[ru] = rv
        par[ru] = pu ^ pv ^ odd

    n = len(ia)
    inv_a = np.empty(n, dtype=np.int64)
    inv_a[ia] = np.arange(n)
    for g in range(n):
        union(int(oa[g]), na + nb + int(oP[g]), 1)
    for h in range(n):
        union(na + int(ob[h]), na + nb + int(oP[inv_a[h]]), 1)
    roots = {find(u) for u in range(n_f)}
    bad_roots = {find(u) for u in bad}
    return len(roots - bad_roots), len(roots)


def word(letters, alpha, beta, p):
    """Product of the letters, left to right, as group elements."""
    g = norm_elt((1, 0, 0, 1), p)
    for ch in letters:
        g = mul(g, alpha if ch == "a" else beta, p)
    return g


def comm(x, y, p):
    return mul(mul(x, y, p), mul(inv(x, p), inv(y, p), p), p)


def face_matrix(ia, oa, ob, oP, na, nb, nP):
    """F: R^{2N} (theta_a, theta_b) -> R^{faces}, the holonomy around each face."""
    n = len(ia)
    rows, cols = [], []
    g = np.arange(n)
    rows.append(oa[g]); cols.append(g)                      # a-faces
    rows.append(na + ob[g]); cols.append(n + g)             # b-faces
    rows.append(na + nb + oP[g]); cols.append(g)            # P-faces: a-edge at g
    rows.append(na + nb + oP[g]); cols.append(n + ia[g])    #          b-edge at alpha g
    return sp.csr_matrix((np.ones(4 * n), (np.concatenate(rows), np.concatenate(cols))),
                         shape=(na + nb + nP, 2 * n))


def gauge_solve(F, ca, cb, cP):
    """Solve F theta = c for theta = (theta_a, theta_b) in R^{2N}."""
    n = F.shape[1] // 2
    c = np.concatenate([ca, cb, cP])
    sol = lsqr(F, c, atol=1e-15, btol=1e-15, iter_lim=20000)
    theta = sol[0]
    res = np.abs(F @ theta - c).max()
    return theta[:n], theta[n:], res


def run(p, seed, Rs):
    alpha, beta, elts, dist = find_triple(p, seed)
    N = len(elts)
    idx = {e: i for i, e in enumerate(elts)}
    ia = np.array([idx[mul(alpha, e, p)] for e in elts], dtype=np.int64)
    ib = np.array([idx[mul(beta, e, p)] for e in elts], dtype=np.int64)
    d = np.array([dist[e] for e in elts], dtype=np.float64)
    iP = ib[ia]
    oa, ra = orbits(ia)
    ob, rb = orbits(ib)
    oP, rP = orbits(iP)
    na, nb, nP = len(ra), len(rb), len(rP)
    print(f"\n=== p = {p}: G = PSL_2(F_{p}), N = {N}, diameter = {int(d.max())}")
    print(f"  orders: alpha {order(alpha, p)}, beta {order(beta, p)}, beta*alpha {order(mul(beta, alpha, p), p)}")
    print(f"  faces: a {na} (=N/4: {na * 4 == N}), b {nb} (=N/3: {nb * 3 == N}), P {nP} (=N/5: {nP * 5 == N})")
    kd, ncomp = kernel_dim_FT(ia, ib, oa, ob, oP, na, nb, nP)
    F = face_matrix(ia, oa, ob, oP, na, nb, nP)
    sign = np.concatenate([np.ones(na + nb), -np.ones(nP)])
    in_ker = bool(np.all(F.T @ sign == 0))
    print(f"  dim ker F^T = {kd} (face components {ncomp}); sign vector (+1,+1,-1) in ker F^T: {in_ker}")
    assert kd == 1 and in_ker

    # Thompson relator r1 = [b a b, a a b a b a a], words read as products left to right
    u = word("bab", alpha, beta, p)
    v = word("aababaa", alpha, beta, p)
    one = norm_elt((1, 0, 0, 1), p)
    r1 = comm(u, v, p)
    ur = word("bab"[::-1], alpha, beta, p)
    vr = word("aababaa"[::-1], alpha, beta, p)
    r1r = comm(ur, vr, p)
    print(f"  Thompson relator [bab, a^2 baba^2] trivial in G? {r1 == one} (reversed convention: {r1r == one})")
    assert r1 != one and r1r != one

    # Markov operator and spectral gap
    I = np.arange(N)
    rows = np.concatenate([ia, ib, I, I])
    cols = np.concatenate([I, I, ia, ib])
    M = sp.csr_matrix((np.full(4 * N, 0.25), (rows, cols)), shape=(N, N))
    vals = eigsh(M, k=3, which="LA", return_eigenvectors=False, tol=1e-10)
    vals = np.sort(vals)[::-1]
    lam2 = vals[1]
    kappa = math.sqrt(2 * (1 - lam2))
    print(f"  Markov top eigenvalues {np.round(vals, 6)}; lambda_2 = {lam2:.6f}; kappa >= {kappa:.4f}")

    eps = 60 * math.pi / (47 * N)
    for R in Rs:
        phi = math.pi * np.maximum(0.0, 1.0 - d / R)
        ca = phi[np.array(ra)]
        cb = phi[np.array(rb)]
        cP = 3 * phi[np.array(rP)]
        S = ca.sum() + cb.sum() - cP.sum()
        m = round(S / (2 * math.pi))
        delta = S - 2 * math.pi * m
        ca = ca.copy()
        ca[0] -= 2 * math.pi * m
        nf = na + nb + nP
        ca -= delta / nf
        cb = cb - delta / nf
        cP = cP + delta / nf
        tha, thb, res = gauge_solve(F, ca, cb, cP)
        hol_a = tha + tha[ia] + tha[ia[ia]] + tha[ia[ia[ia]]]
        hol_b = thb + thb[ib] + thb[ib[ib]]
        hol_P = np.zeros(N)
        gj = I.copy()
        for _ in range(5):
            hol_P += tha[gj] + thb[ia[gj]]
            gj = iP[gj]
        X4 = np.exp(1j * hol_a)
        Y3 = np.exp(1j * hol_b)
        P5 = np.exp(1j * hol_P)
        D = np.exp(1j * phi)
        d1 = np.abs(X4 - Y3).max()
        d2 = np.abs(P5 - X4 ** 3).max()
        d3 = np.abs(X4 - D).max()
        w = np.abs(D - 1) ** 2
        print(f"  R = {R:2d}: |delta| = {abs(delta):.3f}, lsqr residual {res:.1e}; "
              f"||X^4-Y^3|| = {d1:.4f} (bound {3 * math.pi / R + 2 * eps:.4f}), "
              f"||(YX)^5-X^12|| = {d2:.4f} (bound {18 * math.pi / R + 4 * eps:.4f}), "
              f"||X^4-D|| = {d3:.4f} (bound {2 * math.pi / R + eps:.4f}), "
              f"||X^4-1|| = {np.abs(X4 - 1).max():.4f}, tau(w) = {w.mean():.2e}")
        assert res < 1e-8
        assert d1 <= 3 * math.pi / R + 2 * eps + 1e-9
        assert d2 <= 18 * math.pi / R + 4 * eps + 1e-9
        assert d3 <= 2 * math.pi / R + eps + 1e-9
    return lam2


def scalar_ansatz():
    m = Fraction(12)
    a, b = m / 4, m / 3
    print(f"\nScalar ansatz X = D^a alpha, Y = D^b beta: X^4 ~ D^{4 * a}, Y^3 ~ D^{3 * b}, "
          f"(YX)^5 ~ D^{5 * (a + b)} versus X^12 ~ D^{3 * m}: equal? {5 * (a + b) == 3 * m}")
    print("  (5(a+b) = 35m/12 != 36m/12 = 3m for m != 0; the gap m/12 is the Euler number -1/60 times -5m.)")


def main():
    print("Brieskorn gauge pairs: X = M_a L(alpha), Y = M_b L(beta) on l^2(PSL_2(F_p))")
    scalar_ansatz()
    for p in [31, 41, 71, 79]:
        assert p % 8 in (1, 7) and p % 5 in (1, 4)
        N = p * (p * p - 1) // 2
        R0 = int(math.floor(math.log(N, 4) / 2))
        run(p, seed=p, Rs=sorted({R0, 4, 8, 12}))
    print("\nall assertions passed")


if __name__ == "__main__":
    main()
