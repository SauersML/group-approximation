#!/usr/bin/env python3
"""Audit of the i.i.d.-forest gap theorem on the certified split-ansatz parameters.

Theorem (research/thompson-f-iid-forest-test-vectors-are-bounded-below-one.md): for every
i.i.d. pointed-forest test vector (bulk tree law pi, pointer weight y, unit-normalised),
    lim_n Rayleigh/4 = (b^2 + m)/2,  b = <u,y>,  m = <J(y (x) u), y>,  u = sqrt(pi),
and
    2*eps1 + eps2 >= H_tree >= H_size >= sup_t |phi - phi^2| / 2 >= 1/8,
with eps1 = ||y - u||, eps2 = ||J(y (x) u) - y||, H_tree = ||u - J(u (x) u)||,
H_size = Hellinger(nu, nu*nu), nu the size law of pi, phi its characteristic function.
Hence (b^2 + m)/2 <= 1 - 1/1280.

This script evaluates every quantity in the chain, in floating point, for the parameter files of
experiments/thompson-f-norm-ansatz-2026-09-17 (params_N40.json, params_N80.json), to show where
the certified vectors sit in it. Pure Python + math; runs in a few seconds.
"""
import json, math, cmath, sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, '..', 'thompson-f-norm-ansatz-2026-09-17')


def load(path):
    d = json.load(open(path))
    N, sc = d['N'], 2.0 ** d['bits']
    phi = {(l, r): v / sc for l, r, v in d['phi']}
    g = {(l, r): v / sc for l, r, v in d['g']}
    return N, d['x1'] / sc, d['y1'] / sc, phi, g


def audit(path):
    N, x1, y1, phi, g = load(path)
    # size sums: A_s = sum x^2, Bq_s = sum y^2, X_s = sum x y, M_s = sum_{T=(L,R)} y(L) x(R) y(T),
    # C_s = sum_{T=(L,R)} x(L) x(R) x(T)  (the <u, J(u(x)u)> numerator)
    A = [0.0] * (N + 1); Bq = [0.0] * (N + 1); X = [0.0] * (N + 1)
    M = [0.0] * (N + 1); C = [0.0] * (N + 1)
    A[1], Bq[1], X[1] = x1 * x1, y1 * y1, x1 * y1
    for s in range(2, N + 1):
        for l in range(1, s):
            r = s - l
            p, q = phi[(l, r)], g[(l, r)]
            A[s] += p * p * A[l] * A[r]
            Bq[s] += q * q * Bq[l] * A[r]
            X[s] += p * q * X[l] * A[r]
            M[s] += q * Bq[l] * A[r]
            C[s] += p * A[l] * A[r]
    sA, sB = sum(A), sum(Bq)
    rho = 1 / math.sqrt(sA)            # renewal normalisation sum_s rho^2 A_s = 1
    b = rho * sum(X) / math.sqrt(sB)   # <u, y> with y unit
    m = rho * sum(M) / sB              # <J(y(x)u), y>
    ray = (b * b + m) / 2              # lim_n Rayleigh / 4
    eps1 = math.sqrt(max(0.0, 2 - 2 * b))
    eps2 = math.sqrt(max(0.0, 2 - 2 * m))
    Htree = math.sqrt(max(0.0, 2 - 2 * rho ** 3 * sum(C)))
    nu = [a / sA for a in A]           # size law, nu[0] = 0
    nn = [0.0] * (2 * N + 1)
    for i in range(1, N + 1):
        for j in range(1, N + 1):
            nn[i + j] += nu[i] * nu[j]
    nu2 = nu + [0.0] * N
    Hsize = math.sqrt(sum((math.sqrt(a) - math.sqrt(c)) ** 2 for a, c in zip(nu2, nn)))
    best = 0.0
    K = 20000
    for k in range(K + 1):
        t = 2 * math.pi * k / K
        ph = sum(nu[s] * cmath.exp(1j * s * t) for s in range(1, N + 1))
        best = max(best, abs(ph - ph * ph))
    mean = sum(s * nu[s] for s in range(N + 1))
    print(f"{os.path.basename(path)}: N={N}")
    print(f"  lim Rayleigh/4 = (b^2+m)/2 = {ray:.6f}   (b={b:.6f}, m={m:.6f})")
    print(f"  eps1={eps1:.5f} eps2={eps2:.5f}  2eps1+eps2={2*eps1+eps2:.5f}")
    print(f"  H_tree={Htree:.5f} >= H_size={Hsize:.5f} >= sup|phi-phi^2|/2={best/2:.5f} >= 1/8")
    print(f"  mean bulk tree size={mean:.3f}, nu(1)={nu[1]:.4f}")
    assert 2 * eps1 + eps2 >= Htree - 1e-12 >= Hsize - 2e-12 >= best / 2 - 3e-12 >= 0.125 - 3e-12
    assert ray <= 1 - 1 / 1280
    return ray


if __name__ == '__main__':
    paths = sys.argv[1:] or [os.path.join(SRC, 'params_N40.json'), os.path.join(SRC, 'params_N80.json')]
    for p in paths:
        audit(p)
    print("chain verified; universal ceiling 1 - 1/1280 =", 1 - 1 / 1280)
