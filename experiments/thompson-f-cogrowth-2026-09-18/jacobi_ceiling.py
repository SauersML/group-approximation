#!/usr/bin/env python3
"""The ceiling of the cogrowth-moment route for Thompson's F, realised by an explicit
16-atom measure.

With M_j = c_j/16^j for j = 0..31 (Elvey Price--Guttmann), let V = R[x]_{<=15} carry the
inner product <p,q> = L(pq), L the linear functional with L(x^j) = M_j (well defined for
deg <= 31).  This is positive definite because the Hankel matrix (M_{i+j})_{i,j<=15} is
(checked exactly here).  Let J be the matrix, in the orthonormal basis of the orthogonal
polynomials p_0..p_15, of "multiply by x then project back to V": J is symmetric
tridiagonal with entries a_k = L(x p_k^2)/h_k and b_k = sqrt(h_k/h_{k-1}), h_k = L(p_k^2),
all of them exact rationals (b_k^2 is).

Two elementary facts, proved in the route node:
  (1) <J^k e_0, e_0> = M_k/M_0 for every k <= 31, so the spectral measure of J at e_0,
      scaled by M_0, is a measure with exactly the 32 known moments, supported on the 16
      eigenvalues of J;
  (2) <Jv, v> = L(x q^2) for the polynomial q of v, so theta*I - J is positive definite
      exactly when the localizing matrix (theta M_{i+j} - M_{i+j+1})_{i,j<=15} is.

Hence min { sup supp nu : nu >= 0 with these 32 moments } is the largest eigenvalue of J,
and that is the exact optimum of the whole moment route.  This script prints the exact
rational Jacobi data, the eigenvalues and weights in floating point, and checks that the
16-atom measure reproduces all 32 moments.
"""
import json
import math
import os
import sys
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from moment_ceiling import EPG, ldl, localizing, optimum  # noqa: E402


def jacobi(M, d):
    """Exact a_0..a_d, h_0..h_d and b_k^2 = h_k/h_{k-1} from M_0..M_{2d+1}."""
    polys = [[Fraction(1)]]
    a, h, b2 = [], [], []
    prev = [Fraction(0)]
    for k in range(d + 1):
        p = polys[-1]
        hk = sum(p[i] * p[j] * M[i + j] for i in range(len(p)) for j in range(len(p)))
        ak = sum(p[i] * p[j] * M[i + j + 1] for i in range(len(p)) for j in range(len(p))) / hk
        h.append(hk)
        a.append(ak)
        if k:
            b2.append(h[k] / h[k - 1])
        if k < d:
            xp = [Fraction(0)] + p
            n = max(len(xp), len(p), len(prev))
            xp += [Fraction(0)] * (n - len(xp))
            pp = p + [Fraction(0)] * (n - len(p))
            pv = prev + [Fraction(0)] * (n - len(prev))
            beta = h[k] / h[k - 1] if k else Fraction(0)
            polys.append([xp[i] - ak * pp[i] - beta * pv[i] for i in range(n)])
            prev = p
    return a, h, b2


def main():
    M = [Fraction(x, 16 ** j) for j, x in enumerate(EPG)]
    N = 31
    d = 15
    a, h, b2 = jacobi(M, d)
    assert all(x > 0 for x in h), "Hankel not positive definite"

    lo, hi = optimum(M, N)
    # (2): theta I - J psd  <=>  localizing matrix psd; check both at hi
    assert ldl(localizing(M, N, hi)) is None

    A = np.zeros((d + 1, d + 1))
    for k in range(d + 1):
        A[k, k] = float(a[k])
    for k in range(d):
        A[k, k + 1] = A[k + 1, k] = math.sqrt(float(b2[k]))
    w, V = np.linalg.eigh(A)
    weights = (V[0, :] ** 2) * float(M[0])

    rec = [float(sum(weights * w ** j)) for j in range(N + 1)]
    rel = [abs(rec[j] - float(M[j])) / float(M[j]) for j in range(N + 1)]

    out = {
        "moments": N + 1,
        "jacobi_a": [f"{x.numerator}/{x.denominator}" for x in a],
        "jacobi_b_squared": [f"{x.numerator}/{x.denominator}" for x in b2],
        "nodes": [float(x) for x in w],
        "weights": [float(x) for x in weights],
        "weights_all_positive": bool((weights > 0).all()),
        "nodes_in_unit_interval": bool((w > 0).all() and (w < 1).all()),
        "max_relative_moment_error_of_16_atom_measure": max(rel),
        "largest_node": float(w[-1]),
        "theta_star_lower_exact": f"{lo.numerator}/{lo.denominator}",
        "theta_star_upper_exact": f"{hi.numerator}/{hi.denominator}",
        "theta_star_float": [float(lo), float(hi)],
        "ceiling_on_rho": math.sqrt(float(hi)),
        "certified_rho": math.sqrt(float(lo)),
        "reading": ("the 16-atom measure with these nodes and weights has exactly the 32 "
                    "published cogrowth moments and sup supp = largest node, so no argument "
                    "that uses only c_0..c_31 can push ||P|| above sqrt(largest node)."),
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
