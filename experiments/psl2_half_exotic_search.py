#!/usr/bin/env python3
"""Adversarial search for exotic near-solutions of the amalgam presentation of PSL_2(Z[1/2]).

PSL_2(Z[1/2]) = < x, y, x', y' | x^2 = y^3 = x'^2 = y'^3 = 1,
                                   x y = (x' y')^2,
                                   x y^2 x y x = x' y' x' y'^2 x' >.
(Two copies of C_2 * C_3 = PSL_2(Z), glued along Gamma_0(2)/+- = <T = xy, eps = x y^2 x y x>
 = Z * C_2 via T -> T'^2 = (x'y')^2 and eps -> T'^2 V'^-1 = x' y' x' y'^2 x'.)

We keep the finite-order relations EXACT by parametrizing x = V_x D_x V_x^*, y = V_y D_y V_y^*
with fixed diagonal spectral models, and minimize the two gluing defects in normalized HS.
Flexible HS-stability of SL_2(Z[1/2]) (the Dogon-Vigdorovich question) predicts that every
low-defect tuple is close to a congruence representation (a representation of PSL_2(Z/m),
m odd).  A congruence indicator: in a congruence representation the parabolic T = xy has
finite odd order m <= about 2d+1, so  ind = min_{m odd <= 4d} ||(xy)^m - 1||_2  is small.
Exotic near-solutions would have small defect and large ind.

Spectral models: 'balanced' (trace-zero involution, equidistributed cube roots) which is the
regular-character profile, and 'steinberg-like' profiles.
"""

from __future__ import annotations

import json
import sys
import time

import numpy as np
from scipy.optimize import minimize


def hs(A):
    return float(np.sqrt(np.real(np.trace(A.conj().T @ A)) / A.shape[0]))


def cayley(K):
    I = np.eye(K.shape[0])
    return np.linalg.solve(I + K, I - K)


def skew_from_vec(v, d):
    # v real vector of length d*d: first d*(d-1)/2 real parts, then imaginary parts, then diag imag
    n = d * (d - 1) // 2
    K = np.zeros((d, d), dtype=complex)
    iu = np.triu_indices(d, 1)
    K[iu] = v[:n] + 1j * v[n:2 * n]
    K = K - K.conj().T
    K[np.diag_indices(d)] = 1j * v[2 * n:2 * n + d]
    return K


def models(d, kind):
    if kind == "balanced":
        dx = np.array([1.0] * (d // 2) + [-1.0] * (d - d // 2))
        w = np.exp(2j * np.pi / 3)
        k = d // 3
        dy = np.array([1.0] * (d - 2 * k) + [w] * k + [w ** 2] * k)
    else:  # steinberg-like: involution with (d+1)/2 ones, order 3 with unequal parts
        dx = np.array([1.0] * ((d + 1) // 2) + [-1.0] * (d - (d + 1) // 2))
        w = np.exp(2j * np.pi / 3)
        k = d // 3
        dy = np.array([1.0] * (d - 2 * k + (d % 3 == 2)) + [w] * (k - (d % 3 == 2)) + [w ** 2] * k)
        dy = dy[:d]
    return np.diag(dx.astype(complex)), np.diag(dy.astype(complex))


def build(v, d, Dx, Dy):
    m = d * d
    Vs = [cayley(skew_from_vec(v[i * m:(i + 1) * m], d)) for i in range(4)]
    x = Vs[0] @ Dx @ Vs[0].conj().T
    y = Vs[1] @ Dy @ Vs[1].conj().T
    xp = Vs[2] @ Dx @ Vs[2].conj().T
    yp = Vs[3] @ Dy @ Vs[3].conj().T
    return x, y, xp, yp


def defects(x, y, xp, yp):
    T = x @ y
    Tp = xp @ yp
    r1 = T - Tp @ Tp
    eps = x @ y @ y @ x @ y @ x
    epsp = xp @ yp @ xp @ yp @ yp @ xp
    r2 = eps - epsp
    return hs(r1), hs(r2)


def objective(v, d, Dx, Dy):
    x, y, xp, yp = build(v, d, Dx, Dy)
    a, b = defects(x, y, xp, yp)
    return a * a + b * b


def congruence_indicator(x, y, d):
    T = x @ y
    best = 9.0
    best_m = None
    P = np.eye(d, dtype=complex)
    for m in range(1, 4 * d + 2):
        P = P @ T
        if m % 2 == 1:
            val = hs(P - np.eye(d))
            if val < best:
                best, best_m = val, m
    return best, best_m


def run(d, kind, restarts, iters, rng):
    Dx, Dy = models(d, kind)
    m = d * d
    results = []
    for r in range(restarts):
        v0 = rng.normal(size=4 * m) * 0.7
        res = minimize(objective, v0, args=(d, Dx, Dy), method="L-BFGS-B",
                       options={"maxiter": iters, "maxfun": iters * 50})
        x, y, xp, yp = build(res.x, d, Dx, Dy)
        a, b = defects(x, y, xp, yp)
        ind, mbest = congruence_indicator(x, y, d)
        trT = complex(np.trace(x @ y) / d)
        results.append({"d": d, "kind": kind, "restart": r, "defect1": a, "defect2": b,
                        "defect": max(a, b), "cong_ind": ind, "cong_m": mbest,
                        "tr_T": [trT.real, trT.imag], "nit": int(res.nit)})
        print(json.dumps(results[-1]))
        sys.stdout.flush()
    return results


def main():
    rng = np.random.default_rng(1)
    out = []
    t0 = time.time()
    for d, kind, restarts, iters in [(6, "balanced", 12, 400), (6, "steinberg", 8, 400),
                                     (12, "balanced", 10, 400), (12, "steinberg", 6, 400),
                                     (18, "balanced", 6, 300)]:
        out += run(d, kind, restarts, iters, rng)
        print(f"# elapsed {time.time()-t0:.0f}s")
        sys.stdout.flush()
    with open("experiments/psl2-half-exotic-search.json", "w") as fh:
        json.dump(out, fh, indent=1)
    print("DONE-SENTINEL")


if __name__ == "__main__":
    main()
