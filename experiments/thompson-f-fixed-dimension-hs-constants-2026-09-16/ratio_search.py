#!/usr/bin/env python3
"""Verified lower bounds for the fixed-dimension HS commutator constants of Thompson's F.

For U, W in U(n) put, in normalized Hilbert--Schmidt norm,

    e(g) = ||g - I||_2^2 = 2 - 2 Re tr_n(g),

with R1 = [ab^-1, a^-1ba], R2 = [ab^-1, a^-2ba^2] and c = [a,b]. The optimal
fixed-dimension constant is

    C_n = sup_{U,W in U(n)} sqrt( e(c) / max(e(R1), e(R2)) ).

Step 1 (floating point, heuristic): maximize the ratio over Cayley-parametrized
pairs U = (I-K)(I+K)^-1, K skew-Hermitian, subject to a floor e(c) >= tau.
Step 2 (exact, rigorous): round K to Gaussian rationals, rebuild U and W exactly
over Q(i) (they are exactly unitary), and evaluate e(c), e(R1), e(R2) as exact
rationals. Every reported `verified_ratio` is therefore a proved lower bound
C_n >= sqrt(e_c / max(e_R1, e_R2)). Nothing here is an upper bound; a bounded
search that finds no large ratio proves nothing about C_n.

Single-threaded; run with `timeout 600`.
"""

import argparse
import json
import time
from fractions import Fraction as Q

import numpy as np
from scipy.optimize import minimize

# ---------------------------------------------------------------- float side


def cayley(K):
    n = K.shape[0]
    eye = np.eye(n)
    return (eye - K) @ np.linalg.inv(eye + K)


def skew_from_params(p, n):
    H = np.zeros((n, n), dtype=complex)
    idx = 0
    for i in range(n):
        H[i, i] = p[idx]
        idx += 1
    for i in range(n):
        for j in range(i + 1, n):
            H[i, j] = p[idx] + 1j * p[idx + 1]
            H[j, i] = p[idx] - 1j * p[idx + 1]
            idx += 2
    return 1j * H


def words_float(U, W):
    Ui, Wi = U.conj().T, W.conj().T
    x = U @ Wi
    y = Ui @ W @ U
    z = Ui @ Ui @ W @ U @ U
    R1 = x @ y @ x.conj().T @ y.conj().T
    R2 = x @ z @ x.conj().T @ z.conj().T
    c = U @ W @ Ui @ Wi
    return R1, R2, c


def e_float(g):
    n = g.shape[0]
    return 2.0 - 2.0 * np.real(np.trace(g)) / n


def ratio_sq_float(p, n):
    m = n * n
    U = cayley(skew_from_params(p[:m], n))
    W = cayley(skew_from_params(p[m:], n))
    R1, R2, c = words_float(U, W)
    return e_float(c), max(e_float(R1), e_float(R2)), e_float(R1), e_float(R2)


def objective(p, n, tau, power):
    """-log(e_c / ||(e_R1, e_R2)||_power) plus a floor penalty on e_c.

    power = 1 is the sum surrogate; a large power approximates the max, and
    power = inf uses the max itself (for the derivative-free polish).
    """
    ec, emax, e1, e2 = ratio_sq_float(p, n)
    if np.isinf(power):
        den = emax + 1e-14
    else:
        s = max(e1, e2, 1e-300)
        den = s * ((e1 / s) ** power + (e2 / s) ** power) ** (1.0 / power) + 1e-14
    pen = 0.0
    if ec < tau:
        pen = 1e3 * (tau - ec) ** 2 / tau ** 2
    return -(np.log(max(ec, 1e-300)) - np.log(den)) + pen


# ---------------------------------------------------------------- exact side


def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def gconj(a):
    return (a[0], -a[1])


ZERO = (Q(0), Q(0))
ONE = (Q(1), Q(0))


def mmul(A, B):
    n = len(A)
    return [[_rowcol(A, B, i, j, n) for j in range(n)] for i in range(n)]


def _rowcol(A, B, i, j, n):
    s = ZERO
    for k in range(n):
        s = gadd(s, gmul(A[i][k], B[k][j]))
    return s


def mstar(A):
    n = len(A)
    return [[gconj(A[j][i]) for j in range(n)] for i in range(n)]


def minv_exact(A):
    """Gauss--Jordan inverse over Q(i)."""
    n = len(A)
    M = [row[:] + [ONE if i == j else ZERO for j in range(n)] for i, row in enumerate(A)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != ZERO)
        M[col], M[piv] = M[piv], M[col]
        a = M[col][col]
        norm = a[0] * a[0] + a[1] * a[1]
        inv = (a[0] / norm, -a[1] / norm)
        M[col] = [gmul(inv, v) for v in M[col]]
        for r in range(n):
            if r != col and M[r][col] != ZERO:
                f = M[r][col]
                M[r] = [gadd(M[r][k], gmul((-f[0], -f[1]), M[col][k])) for k in range(2 * n)]
    return [row[n:] for row in M]


def exact_skew(p, n, den):
    """K = i H with H Hermitian, entries rounded to multiples of 1/den."""
    K = [[ZERO] * n for _ in range(n)]
    idx = 0
    diag = []
    for i in range(n):
        diag.append(Q(round(p[idx] * den), den))
        idx += 1
    for i in range(n):
        K[i][i] = (Q(0), diag[i])  # i * real
    for i in range(n):
        for j in range(i + 1, n):
            re = Q(round(p[idx] * den), den)
            im = Q(round(p[idx + 1] * den), den)
            idx += 2
            # H_ij = re + i im, K_ij = i H_ij = -im + i re; K_ji = -conj(K_ij)
            K[i][j] = (-im, re)
            K[j][i] = (im, re)
    return K


def exact_cayley(K):
    n = len(K)
    Im = [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]
    minus = [[gadd(Im[i][j], (-K[i][j][0], -K[i][j][1])) for j in range(n)] for i in range(n)]
    plus = [[gadd(Im[i][j], K[i][j]) for j in range(n)] for i in range(n)]
    return mmul(minus, minv_exact(plus))


def e_exact(g):
    n = len(g)
    tr = Q(0)
    for i in range(n):
        tr += g[i][i][0]
    return 2 - 2 * tr / n


def verify(p, n, den):
    m = n * n
    U = exact_cayley(exact_skew(p[:m], n, den))
    W = exact_cayley(exact_skew(p[m:], n, den))
    Ui, Wi = mstar(U), mstar(W)
    # exact unitarity check
    Im = [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]
    assert mmul(U, Ui) == Im and mmul(W, Wi) == Im
    x = mmul(U, Wi)
    y = mmul(mmul(Ui, W), U)
    z = mmul(mmul(mmul(mmul(Ui, Ui), W), U), U)
    R1 = mmul(mmul(mmul(x, y), mstar(x)), mstar(y))
    R2 = mmul(mmul(mmul(x, z), mstar(x)), mstar(z))
    c = mmul(mmul(mmul(U, W), Ui), Wi)
    return e_exact(c), e_exact(R1), e_exact(R2)


# ---------------------------------------------------------------- driver


def search(n, tau, restarts, rng, budget):
    m = n * n
    best = None
    t0 = time.time()
    for r in range(restarts):
        if time.time() - t0 > budget:
            break
        scale = rng.choice([0.3, 1.0, 3.0])
        p0 = rng.normal(scale=scale, size=2 * m)
        res = minimize(objective, p0, args=(n, tau, 1.0), method="L-BFGS-B",
                       options={"maxiter": 400})
        res = minimize(objective, res.x, args=(n, tau, 16.0), method="L-BFGS-B",
                       options={"maxiter": 400})
        res = minimize(objective, res.x, args=(n, tau, np.inf), method="Nelder-Mead",
                       options={"maxiter": 4000, "xatol": 1e-10, "fatol": 1e-14})
        ec, emax, _, _ = ratio_sq_float(res.x, n)
        if ec < 0.9 * tau or emax <= 1e-9:
            continue
        val = ec / emax
        if best is None or val > best[0]:
            best = (val, res.x.copy())
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dims", default="2,3,4")
    ap.add_argument("--taus", default="0.01,0.1,0.5")
    ap.add_argument("--restarts", type=int, default=12)
    ap.add_argument("--budget", type=float, default=40.0)
    ap.add_argument("--den", type=int, default=10**5)
    ap.add_argument("--seed", type=int, default=20260916)
    ap.add_argument("--out", default="ratio_search.json")
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    rows = []
    for n in [int(s) for s in args.dims.split(",")]:
        for tau in [float(s) for s in args.taus.split(",")]:
            best = search(n, tau, args.restarts, rng, args.budget)
            if best is None:
                rows.append({"n": n, "tau": tau, "found": False})
                continue
            ec, e1, e2 = verify(best[1], n, args.den)
            emax = max(e1, e2)
            row = {
                "n": n,
                "tau": tau,
                "found": True,
                "float_ratio": float(np.sqrt(best[0])),
                "exact_e_c_float": float(ec),
                "exact_e_R1_float": float(e1),
                "exact_e_R2_float": float(e2),
                "verified_ratio": float(np.sqrt(float(ec) / float(emax))) if emax > 0 else None,
                "cayley_params_rounded_den": args.den,
                "params": [round(float(v) * args.den) for v in best[1]],
            }
            rows.append(row)
            print(json.dumps({k: row[k] for k in row if k != "params"}), flush=True)
    with open(args.out, "w") as fh:
        json.dump({"seed": args.seed, "rows": rows}, fh, indent=1)


if __name__ == "__main__":
    main()
