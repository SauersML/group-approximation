#!/usr/bin/env python3
"""Cross-check the size-law reduction against the w13 window machinery (certify_window.py).

For random size laws alpha, beta on {1..N} build the split weights of the route
    phi(s,t) = sqrt(alpha_j beta_s / (alpha_s (beta*alpha)_j)),  g(s,t) = sqrt(beta_j / (beta*alpha)_j),
    x1 = sqrt(alpha_1), y1 = sqrt(beta_1),   j = s + t,
feed them (as exact Fractions of the floats) to certify_window.exact_sums, and compare
  * the shape sums A_s, Bq_s, X_s, sum_{k+l=j} M_{k,l} with alpha_s, beta_s, sqrt(alpha_s beta_s),
    sqrt(beta_j (alpha*beta)_j);
  * the exact finite-window quotients Num_n/D_n (certify_window.exact_ratio) with J(alpha, beta);
    they must increase towards J like 1/n.
"""
import sys
import random
from fractions import Fraction as Fr
import numpy as np

sys.path.insert(0, "../thompson-f-norm-ansatz-2026-09-17")
import certify_window as cw  # noqa: E402
from size_law_problem import J_and_grad  # noqa: E402

rng = random.Random(7)
for trial in range(3):
    N = [6, 9, 12][trial]
    al = np.array([rng.random() + 0.2 for _ in range(N)]); al /= al.sum()
    be = np.array([rng.random() + 0.2 for _ in range(N)]); be /= be.sum()
    c = np.convolve(be, al)  # c[m] = size m + 2
    phi, g = {}, {}
    for s in range(1, N):
        for t in range(1, N - s + 1):
            j = s + t
            cj = c[j - 2]
            phi[s, t] = Fr(float(np.sqrt(al[j - 1] * be[s - 1] / (al[s - 1] * cj))))
            g[s, t] = Fr(float(np.sqrt(be[j - 1] / cj)))
    x1, y1 = Fr(float(np.sqrt(al[0]))), Fr(float(np.sqrt(be[0])))
    A, Bq, X, M = cw.exact_sums(phi, g, x1, y1, N)
    Ms = {}
    for (k, l), v in M.items():
        Ms[k + l] = Ms.get(k + l, 0) + v
    errA = max(abs(float(A[s]) - al[s - 1]) for s in range(1, N + 1))
    errB = max(abs(float(Bq[s]) - be[s - 1]) for s in range(1, N + 1))
    errX = max(abs(float(X[s]) - np.sqrt(al[s - 1] * be[s - 1])) for s in range(1, N + 1))
    errM = max(abs(float(Ms[j]) - np.sqrt(be[j - 1] * c[j - 2])) for j in range(2, N + 1))
    J = J_and_grad(np.sqrt(al), np.sqrt(be))[0]
    # exact window quotients with rho = tau = 1 (p = A, q = Bq, B = X)
    H = {}
    for s in X:
        for t in X:
            H[s + t] = H.get(s + t, Fr(0)) + X[s] * X[t]
    for j, v in Ms.items():
        H[j] = H.get(j, Fr(0)) + v
    ps = sum(A.values())
    lim = 2 * float(sum(H.values())) / float(sum(Bq.values()))
    rs = [float(cw.exact_ratio(A, Bq, H, n)) for n in (50, 100, 200)]
    print(f"N={N}: max shape-sum errors A {errA:.1e} Bq {errB:.1e} X {errX:.1e} M {errM:.1e}; sum p = {float(ps):.15f}")
    print(f"   J(alpha,beta) = {J:.12f}   2H(1)/Q(1) = {lim:.12f}   window Num_n/D_n at n=50,100,200: "
          + ", ".join(f"{r:.9f}" for r in rs)
          + f"   n*(J - ratio): " + ", ".join(f"{n*(J-r):.4f}" for n, r in zip((50, 100, 200), rs)))
