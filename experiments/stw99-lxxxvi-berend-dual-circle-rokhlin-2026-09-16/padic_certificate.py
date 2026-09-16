#!/usr/bin/env python3
"""p-adic certificates (p = 2, 3): torsion orbits whose stabilizer lies in p*Gamma,
for EVERY torsion-free rank-two subgroup Gamma of the unit group O^x, where
O = Z[a] and a is a root of f(t) = t^3 + t^2 - 2t - 1 (basis 1, a, a^2).

Mathematics: research/artifacts/berend-dual-circle-rokhlin-obstruction-2026-09-16.md,
Lemmas 3 and 4.

* For N >= 2 let xi_N be the character z -> exp(2 pi i z_2 / N) of O = Z^3,
  z_2 the a^2-coordinate.  gamma fixes xi_N iff (gamma - 1) O is contained in
  {z : z_2 = 0 mod N}, iff gamma - 1 lies in N O (test z = 1, a, a^2: the
  a^2-coordinates of w, a w, a^2 w are w_2, w_1 - w_2, w_0 - w_1 + 3 w_2).
  So Stab(xi_N) = Gamma cap (1 + N O); xi_N is the vector v = (0,0,1) mod N
  of stabilizers.py / certificate.py.
* p = 2 and p = 3 are inert in O (f has no root mod p), so O_p is an
  unramified DVR with uniformizer p, and log : 1 + p^m O_p -> p^m O_p
  (m = 2 for p = 2, m = 1 for p = 3) is a valuation-preserving isomorphism.
* If log(eps1), log(eps2) are Z_p-linearly independent for two units eps_i in
  1 + p^m O, then for every torsion-free rank-two Gamma <= O^x there is j_0
  with Stab(xi_{p^j}) <= p Gamma for all j >= j_0 (Lemma 4 of the artifact).

This script certifies, for p = 2 (eps = a^14, (a+1)^14) and p = 3
(eps = a^26, (a+1)^26):
  (1) eps_i in 1 + p^m O;
  (2) log(eps_i) modulo p^K via the logarithm series, and a 2x2 minor of the
      coordinate matrix nonzero modulo p^K (so nonzero in Z_p);
  (3) two independent consistency checks: log(eps1 eps2) = log eps1 + log eps2
      and log(eps) = (eps^{p^K} - 1) / p^K modulo p^K;
  (4) for Gamma_+- = <a, +-(a+1)>: exact stabilizers Gamma cap (1 + p^j O),
      their index, whether they lie in p Z^2 (exponent coordinates), and
      for small j agreement with the matrix-side stabilizer of v = (0,0,1).
Pure integer arithmetic, single-threaded, a few seconds.
"""
import json
import sys
from math import gcd

K = 40
MA = ((0, 0, 1), (1, 0, 2), (0, 1, -1))  # multiplication by a, columns a*1, a*a, a*a^2


def mul(x, y, mod):
    # a^3 = -a^2 + 2a + 1,  a^4 = 3a^2 - a - 1
    c = [0] * 5
    for i in range(3):
        for j in range(3):
            c[i + j] += x[i] * y[j]
    r0 = c[0] + c[3] - c[4]
    r1 = c[1] + 2 * c[3] - c[4]
    r2 = c[2] - c[3] + 3 * c[4]
    return (r0 % mod, r1 % mod, r2 % mod)


def power(x, e, mod):
    r = (1 % mod, 0, 0)
    b = tuple(t % mod for t in x)
    while e:
        if e & 1:
            r = mul(r, b, mod)
        b = mul(b, b, mod)
        e >>= 1
    return r


def sanity():
    M = 10 ** 9
    A = (0, 1, 0)
    assert mul(A, (-2 % M, 1, 1), M) == (1, 0, 0)           # a (a^2 + a - 2) = 1
    assert mul((1, 1, 0), (2, 0, M - 1), M) == (1, 0, 0)    # (a+1)(2 - a^2) = 1
    a2 = mul(A, A, M)
    a3 = mul(a2, A, M)
    assert tuple((a3[i] + a2[i] - 2 * A[i] - (1 if i == 0 else 0)) % M for i in range(3)) == (0, 0, 0)
    # a^2-coordinates of w, a w, a^2 w (unitriangular test of the identification)
    w = (5, 7, 11)
    aw, a2w = mul(A, w, M), mul(a2, w, M)
    assert aw[2] == (w[1] - w[2]) % M and a2w[2] == (w[0] - w[1] + 3 * w[2]) % M


def vp(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def f_has_no_root_mod(p):
    return all((t ** 3 + t ** 2 - 2 * t - 1) % p != 0 for t in range(p))


def minval(p):
    return 2 if p == 2 else 1


def log_series(x, p, K):
    """log(1+x) = sum (-1)^{n+1} x^n / n modulo p^K, x in p^m O_p, m = minval(p).

    Term n has valuation >= m n - v_p(n) > m n - bitlength(n); the lower bound
    m t - log2(t) is nondecreasing for t >= 1, so once m n - bitlength(n) >= K
    all remaining terms vanish modulo p^K.  x^n is computed modulo p^P and is
    divisible by p^{m n}, hence by p^{v_p(n)}; the quotient is correct modulo
    p^{P - v_p(n)}, and we assert v_p(n) <= P - K.
    """
    m = minval(p)
    P = K + 16
    modP, modK = p ** P, p ** K
    assert all(t % (p ** m) == 0 for t in x)
    x = tuple(t % modP for t in x)
    acc = [0, 0, 0]
    xn = (1, 0, 0)
    n = 0
    while True:
        n += 1
        if m * n - n.bit_length() >= K:
            break
        xn = mul(xn, x, modP)
        v = vp(n, p)
        assert v <= P - K
        uinv = pow(n // (p ** v), -1, modK)
        sign = 1 if n % 2 == 1 else -1
        for i in range(3):
            assert xn[i] % (p ** v) == 0
            acc[i] = (acc[i] + sign * (xn[i] // (p ** v)) * uinv) % modK
    return tuple(acc)


def log_by_powering(eps, p, K):
    """(eps^{p^K} - 1) / p^K modulo p^K.

    With L = log eps, eps^{p^K} = exp(p^K L) and (exp(p^K L) - 1)/p^K
    = L + sum_{n>=2} p^{(n-1)K} L^n / n!; the n-th term has valuation
    >= (n-1)K + m n - v_p(n!) >= (n-1)K + m n - (n-1) >= K + 1 for n >= 2.
    """
    mod = p ** (2 * K + 4)
    e = tuple(t % mod for t in eps)
    for _ in range(K):
        e = power(e, p, mod)
    w = ((e[0] - 1) % mod, e[1], e[2])
    assert all(t % (p ** K) == 0 for t in w)
    return tuple((t // (p ** K)) % (p ** K) for t in w)


def order(x, mod):
    one = (1 % mod, 0, 0)
    k, q = 1, tuple(t % mod for t in x)
    while q != one:
        q = mul(q, x, mod)
        k += 1
    return k


def ring_stabilizer(beta, N):
    """eA, eB and the residues (n,m) in [0,eA) x [0,eB) with a^n beta^m = 1 mod N."""
    A = (0, 1, 0)
    Ainv = (-2 % N, 1, 1)
    eA, eB = order(A, N), order(beta, N)
    table = {}
    q = (1 % N, 0, 0)
    for m_ in range(eB):
        table[q] = m_  # powers beta^0..beta^{eB-1} are distinct
        q = mul(q, beta, N)
    res = set()
    q = (1 % N, 0, 0)
    for n in range(eA):
        # a^n beta^m = 1  iff  beta^m = a^{-n}
        if q in table:
            res.add((n, table[q]))
        q = mul(q, Ainv, N)
    return eA, eB, res


def matrix_stabilizer(beta, N, eA, eB):
    """Residues with (M_a^T)^n (M_beta^T)^m v = v mod N, v = (0,0,1)."""
    I3 = tuple(tuple((1 % N) if i == k else 0 for k in range(3)) for i in range(3))

    def mm(X, Y):
        return tuple(tuple(sum(X[i][k] * Y[k][j] for k in range(3)) % N for j in range(3))
                     for i in range(3))

    cols = [tuple(t % N for t in beta), mul(beta, (0, 1, 0), N), mul(beta, (0, 0, 1), N)]
    MB = tuple(tuple(cols[k][i] for k in range(3)) for i in range(3))
    At = tuple(tuple(MA[k][i] % N for k in range(3)) for i in range(3))
    Bt = tuple(tuple(MB[k][i] for k in range(3)) for i in range(3))
    v = (0, 0, 1 % N)
    res = set()
    PA = I3
    for n in range(eA):
        PB = PA
        for m_ in range(eB):
            if tuple(PB[i][2] % N for i in range(3)) == v:
                res.add((n, m_))
            PB = mm(PB, Bt)
        PA = mm(PA, At)
    assert PA == I3
    return res


def lattice_index(eA, eB, res):
    gens = [(eA, 0), (0, eB)] + [r for r in res if r != (0, 0)]
    g = 0
    for s in range(len(gens)):
        for t in range(s + 1, len(gens)):
            g = gcd(g, gens[s][0] * gens[t][1] - gens[s][1] * gens[t][0])
    return g, gens


def certify_prime(p, e, jmax, jmatrix):
    m = minval(p)
    assert f_has_no_root_mod(p)  # cubic without roots mod p: p inert, O_p unramified
    mod = p ** (K + 32)
    eps1 = power((0, 1, 0), e, mod)
    eps2 = power((1, 1, 0), e, mod)
    for eps in (eps1, eps2):
        assert (eps[0] - 1) % (p ** m) == 0 and eps[1] % (p ** m) == 0 and eps[2] % (p ** m) == 0
    L1 = log_series(((eps1[0] - 1) % mod, eps1[1], eps1[2]), p, K)
    L2 = log_series(((eps2[0] - 1) % mod, eps2[1], eps2[2]), p, K)
    e12 = mul(eps1, eps2, mod)
    L12 = log_series(((e12[0] - 1) % mod, e12[1], e12[2]), p, K)
    additive = all((L12[i] - L1[i] - L2[i]) % (p ** K) == 0 for i in range(3))
    assert additive
    powering = (log_by_powering(power((0, 1, 0), e, p ** (2 * K + 4)), p, K) == L1
                and log_by_powering(power((1, 1, 0), e, p ** (2 * K + 4)), p, K) == L2)
    assert powering
    minors = {}
    for (i, k) in ((0, 1), (0, 2), (1, 2)):
        d = (L1[i] * L2[k] - L1[k] * L2[i]) % (p ** K)
        minors[f"{i}{k}"] = {"value_mod_p^K": d, "v_p": (vp(d, p) if d else None)}
    independent = any(dd["v_p"] is not None for dd in minors.values())
    assert independent
    out = {
        "p": p, "K": K, "exponent_e": e,
        "f_has_no_root_mod_p": True,
        "eps1=a^e_and_eps2=(a+1)^e_in_1+p^m_O": True, "m": m,
        "log_eps1_mod_p^K": L1, "log_eps2_mod_p^K": L2,
        "log_additivity_check": additive,
        "log_equals_(eps^(p^K)-1)/p^K_check": powering,
        "minors": minors,
        "Zp_linearly_independent": independent,
        "stabilizers": [],
    }
    for sign, beta in (("b_minus=a+1", (1, 1, 0)), ("b_plus=-(a+1)", (-1, -1, 0))):
        rows, first = [], None
        for j in range(1, jmax + 1):
            N = p ** j
            b = tuple(t % N for t in beta)
            eA, eB, res = ring_stabilizer(b, N)
            idx, gens = lattice_index(eA, eB, res)
            in_p = all(x % p == 0 and y % p == 0 for x, y in gens)
            mcheck = None
            if j <= jmatrix:
                mcheck = (matrix_stabilizer(b, N, eA, eB) == res)
                assert mcheck
            rows.append({"j": j, "N": N, "orders": [eA, eB], "index": idx,
                         "stab_in_pZ2": in_p, "equals_matrix_stabilizer_of_v001": mcheck})
            if in_p and first is None:
                first = j
        out["stabilizers"].append({"sign": sign, "first_j_with_stab_in_pZ2": first, "rows": rows})
    return out


def main():
    sanity()
    info = {"certificates": [certify_prime(2, 14, 8, 5), certify_prime(3, 26, 4, 2)]}
    json.dump(info, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
