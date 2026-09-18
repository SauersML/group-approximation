#!/usr/bin/env python3
"""Rigorous lower bound on ||x0 + x0^-1 + x1 + x1^-1|| from ONE explicit finitely supported test vector.

Support: S_n = pointed forests with n leaves (trivial bottom forest), a subgraph of the Cayley graph of
F (model_check.py; general proof in the route node).  Test vector, for dyadic rationals phi, g, x1, y1
(rounded from split_ansatz.py) and truncation N:
    x(leaf) = rho*x1,  x((L,R)) = phi(|L|,|R|) x(L) x(R) / rho     (so x(T) = rho * x_raw(T)),
    y(leaf) = y1,      y((L,R)) = g(|L|,|R|) y(L) x_raw(R),          x = y = 0 on trees with > N leaves,
    f(T_0..T_{m-1}; i) = y(T_i) prod_{j != i} x(T_j) >= 0.
Since f >= 0 and every move edge of S_n is a Cayley edge, <f, A f> >= <f, A_S f> = Num_n and
||A|| >= Num_n / D_n, D_n = <f, f>.

Shape sums (exact, dyadic rationals): A_s = sum x_raw^2, Bq_s = sum y^2, X_s = sum x_raw y, and
M_{k,l} = g(k,l) Bq_k A_l.  With p = rho^2 A, q = Bq, B = rho X, M' = rho M:
    Z_0 = 1, Z_m = sum_s p_s Z_{m-s};  W = q * Z;  V = H * Z,  H_j = sum_{s+t=j} B_s B_t + sum_{k+l=j} M'_{k,l};
    D_n = sum_l Z_l W_{n-l},  Num_n = 2 sum_l Z_l V_{n-l}.
Every quantity is a sum of products of nonnegative numbers, so evaluating it in fixed point with every
step rounded down (resp. up) gives a rigorous lower bound for Num_n (resp. upper bound for D_n).

Usage: python3 certify_window.py PARAMS.pt N n [bits]      (self-test: python3 certify_window.py test)
"""
import sys, json
from fractions import Fraction as Fr


def dyadic(v, bits=24):
    return Fr(round(v * (1 << bits)), 1 << bits)


def exact_sums(phi, g, x1, y1, N):
    A = {1: x1 * x1}
    Bq = {1: y1 * y1}
    X = {1: x1 * y1}
    M = {}
    for n in range(2, N + 1):
        a = b = c = Fr(0)
        for l in range(1, n):
            r = n - l
            ph, gg = phi[l, r], g[l, r]
            a += ph * ph * A[l] * A[r]
            b += gg * gg * Bq[l] * A[r]
            c += ph * gg * X[l] * A[r]
            M[l, r] = gg * Bq[l] * A[r]
        A[n], Bq[n], X[n] = a, b, c
    return A, Bq, X, M


def fixed(v, P, up):
    q, rem = divmod(v.numerator << P, v.denominator)
    return q + (1 if (up and rem) else 0)


def bounds(p, q, H, n, P, up):
    """Fixed-point evaluation; up=False rounds every step down, up=True rounds every step up."""
    one = 1 << P
    N = max(p)
    ps = [(s, fixed(p[s], P, up)) for s in sorted(p)]
    qs = [(s, fixed(q[s], P, up)) for s in sorted(q)]
    hs = [(j, fixed(H[j], P, up)) for j in sorted(H)]

    def rnd(t):
        return -((-t) >> P) if up else t >> P
    Z = [one]
    for m in range(1, n + 1):
        Z.append(rnd(sum(c * Z[m - s] for s, c in ps if s <= m)))
    W = [rnd(sum(c * Z[k - s] for s, c in qs if s <= k)) for k in range(n + 1)]
    V = [rnd(sum(c * Z[k - j] for j, c in hs if j <= k)) for k in range(n + 1)]
    D = rnd(sum(Z[l] * W[n - l] for l in range(n + 1)))
    Num = 2 * rnd(sum(Z[l] * V[n - l] for l in range(n + 1)))
    return Num, D


def certificate(phi, g, x1, y1, N, n, P=160):
    A, Bq, X, M = exact_sums(phi, g, x1, y1, N)
    # rho ~ 1 / sqrt(sum A) as a dyadic rational (any positive rho is valid)
    sA = sum(A.values())
    rho = dyadic(float(sA) ** -0.5, 40)
    sB = sum(Bq.values())
    tau2 = dyadic(1 / float(sB), 40)  # y-scale; cancels in the ratio, kept for numerical range
    p = {s: rho * rho * A[s] for s in A}
    q = {s: tau2 * Bq[s] for s in Bq}
    B = {s: rho * X[s] for s in X}
    H = {}
    for s in B:
        for t in B:  # pointer tree s and right neighbour t: j = s + t runs up to 2N
            H[s + t] = H.get(s + t, Fr(0)) + tau2 * B[s] * B[t]
    for (k, l), v in M.items():
        H[k + l] = H.get(k + l, Fr(0)) + tau2 * rho * v
    Num_lo, _ = bounds(p, q, H, n, P, up=False)
    _, D_hi = bounds(p, q, H, n, P, up=True)
    return Fr(Num_lo, D_hi), (A, Bq, X, M, rho)


def load(path, N, bits=24):
    """Parameters as dyadic rationals.  From a torch .pt optimiser output, they are rounded to
    multiples of 2^-bits and exported to params_N{N}.json (integer numerators over 2^bits); a
    .json path is read directly, so the certificate itself needs no torch."""
    if path.endswith('.json'):
        d = json.load(open(path))
        den = 1 << d["bits"]
        phi = {(l, r): Fr(v, den) for l, r, v in d["phi"]}
        g = {(l, r): Fr(v, den) for l, r, v in d["g"]}
        assert d["N"] == N
        return phi, g, Fr(d["x1"], den), Fr(d["y1"], den)
    import torch
    lphi, lg, lx1, ly1 = torch.load(path)
    phi, g = {}, {}
    for l in range(1, N):
        for r in range(1, N - l + 1):
            phi[l, r] = dyadic(float(torch.exp(lphi[l, r])), bits)
            g[l, r] = dyadic(float(torch.exp(lg[l, r])), bits)
    x1, y1 = dyadic(float(torch.exp(lx1)), bits), dyadic(float(torch.exp(ly1)), bits)
    sc = 1 << bits
    json.dump({"N": N, "bits": bits, "x1": int(x1 * sc), "y1": int(y1 * sc),
               "phi": [[l, r, int(v * sc)] for (l, r), v in sorted(phi.items())],
               "g": [[l, r, int(v * sc)] for (l, r), v in sorted(g.items())]},
              open(f"params_N{N}.json", "w"))
    return phi, g, x1, y1


def exact_ratio(p, q, H, n):
    Z = [Fr(1)]
    for m in range(1, n + 1):
        Z.append(sum(p[s] * Z[m - s] for s in p if s <= m))
    W = [sum(q[s] * Z[k - s] for s in q if s <= k) for k in range(n + 1)]
    V = [sum(H[j] * Z[k - j] for j in H if j <= k) for k in range(n + 1)]
    return Fr(2 * sum(Z[l] * V[n - l] for l in range(n + 1)), sum(Z[l] * W[n - l] for l in range(n + 1)))


def self_test(N=4, nmax=7):
    """Random dyadic parameters; compare the DP (exact and fixed-point) with brute force over S_n."""
    import random
    sys.path.insert(0, '../thompson-f-cogrowth-2026-09-17')
    from forest_window_scout import forests
    from model_check import moves
    random.seed(1)
    phi = {(l, r): Fr(random.randint(1, 64), 32) for l in range(1, N) for r in range(1, N - l + 1)}
    g = {(l, r): Fr(random.randint(1, 64), 32) for l in range(1, N) for r in range(1, N - l + 1)}
    x1, y1 = Fr(3, 5), Fr(1, 2)
    A, Bq, X, M = exact_sums(phi, g, x1, y1, N)
    rho = Fr(7, 5)

    def nl(t):
        return 1 if t == () else nl(t[0]) + nl(t[1])

    def xr(t):
        if t == ():
            return x1
        if nl(t) > N:
            return Fr(0)
        return phi[nl(t[0]), nl(t[1])] * xr(t[0]) * xr(t[1])

    def yv(t):
        if t == ():
            return y1
        if nl(t) > N:
            return Fr(0)
        return g[nl(t[0]), nl(t[1])] * yv(t[0]) * xr(t[1])

    def f(st):
        fo, i = st
        v = yv(fo[i])
        for j, t in enumerate(fo):
            if j != i:
                v *= rho * xr(t)
        return v
    p = {s: rho * rho * A[s] for s in A}
    q = dict(Bq)
    B = {s: rho * X[s] for s in X}
    H = {}
    for s in B:
        for t in B:
            H[s + t] = H.get(s + t, Fr(0)) + B[s] * B[t]
    for (k, l), v in M.items():
        H[k + l] = H.get(k + l, Fr(0)) + rho * v
    for n in range(2, nmax + 1):
        num = den = Fr(0)
        for fo in forests(n):
            for i in range(len(fo)):
                fs = f((fo, i))
                den += fs * fs
                for _, y2 in moves((fo, i)):
                    num += fs * f(y2)
        dp = exact_ratio(p, q, H, n)
        lo, _ = bounds(p, q, H, n, 64, False)
        _, hi = bounds(p, q, H, n, 64, True)
        assert dp == num / den, (n, dp, num / den)
        assert Fr(lo, hi) <= dp
        print(f"n={n}: brute force = DP = {float(dp):.12f}, fixed-point lower bound {float(Fr(lo, hi)):.12f}")


if __name__ == "__main__":
    if sys.argv[1] == 'test':
        self_test()
    else:
        path, N, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
        P = int(sys.argv[4]) if len(sys.argv) > 4 else 160
        phi, g, x1, y1 = load(path, N)
        lb, _ = certificate(phi, g, x1, y1, N, n, P)
        print(f"N={N} n={n}: ||A|| >= {lb.numerator}/{lb.denominator}")
        print(f"  ||P|| >= {float(lb) / 4:.9f}   (exact rational lower bound on Num_n/D_n, divided by 4)")
        for t in ["0.910677539453", "0.929", "0.93"]:
            print(f"  exceeds {t}: {lb > 4 * Fr(t)}")
        json.dump({"N": N, "n": n, "bits": P, "A_lower_num": str(lb.numerator), "A_lower_den": str(lb.denominator),
                   "P_lower_float": float(lb) / 4}, open(f"certificate_N{N}_n{n}.json", "w"), indent=1)
