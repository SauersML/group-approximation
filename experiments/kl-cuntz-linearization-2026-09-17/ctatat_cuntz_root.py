#!/usr/bin/env python3
"""Root of the census word w0 = c t a t a t^-1 over Thompson's V, inside U(O_2).

Setting (higman-thompson-roots-miss-a-kl-word-over-thompson-v):
  a = (00 01), c = (1 00) in V, F = <a, c> = S_3, acting on the three leaves
  l = (00, 01, 1) of a complete prefix code.  In O_2 = C*(s_0, s_1) the leaf
  isometries s_00, s_01, s_1 form a Cuntz family (orthogonal ranges summing to 1),
  so Phi(M) = sum_ij M_ij s_{l_i} s_{l_j}^* is a unital *-homomorphism M_3 -> O_2,
  and the canonical unitary of g in F is U_g = Phi(P_g), with P_g the leaf
  permutation matrix.  Hence for X in U(3):

      w0(U_a, U_c, Phi(X)) = Phi(w0(P_a, P_c, X)),

  and any X in U(3) with P_c X P_a X P_a X^-1 = I gives the exact root
  T = Phi(X) in U(O_2).  Gerstenhaber--Rothaus guarantees X exists; this script
  finds one numerically, and checks that no permutation matrix is a root
  (the orbit-type obstruction of cantor-homeomorphisms-miss-a-unimodular-root).
"""
import itertools
import json
import sys

import numpy as np
from scipy.linalg import expm
from scipy.optimize import least_squares

LEAVES = ["00", "01", "1"]


def perm_matrix(perm):
    """(P)_{perm[i], i} = 1: leaf i is sent to leaf perm[i]."""
    n = len(perm)
    p = np.zeros((n, n), dtype=complex)
    for i, j in enumerate(perm):
        p[j, i] = 1.0
    return p


P_a = perm_matrix([1, 0, 2])  # swaps 00 and 01
P_c = perm_matrix([2, 1, 0])  # swaps 00 and 1


def word(x):
    return P_c @ x @ P_a @ x @ P_a @ np.linalg.inv(x)


def herm(params):
    h = np.zeros((3, 3), dtype=complex)
    k = 0
    for i in range(3):
        h[i, i] = params[k]
        k += 1
    for i in range(3):
        for j in range(i + 1, 3):
            h[i, j] = params[k] + 1j * params[k + 1]
            h[j, i] = params[k] - 1j * params[k + 1]
            k += 2
    return h


def residual(params):
    x = expm(1j * herm(params))
    r = word(x) - np.eye(3)
    return np.concatenate([r.real.ravel(), r.imag.ravel()])


def main():
    rng = np.random.default_rng(20260917)
    # 1. No permutation root: the orbit type {3} of F on the leaves forbids it.
    perm_roots = []
    for perm in itertools.permutations(range(3)):
        x = perm_matrix(list(perm))
        if np.allclose(word(x), np.eye(3)):
            perm_roots.append(list(perm))
    # 2. Unitary root by least squares from random starts.
    best = None
    for _ in range(200):
        p0 = rng.normal(scale=2.0, size=9)
        sol = least_squares(residual, p0, xtol=1e-15, ftol=1e-15, gtol=1e-15)
        err = float(np.max(np.abs(residual(sol.x))))
        if best is None or err < best[0]:
            best = (err, sol.x)
        if err < 1e-13:
            break
    err, params = best
    x = expm(1j * herm(params))
    unitarity = float(np.max(np.abs(x.conj().T @ x - np.eye(3))))
    opnorm_defect = float(np.linalg.norm(word(x) - np.eye(3), 2))
    out = {
        "word": "c t a t a t^-1 (census ctataT)",
        "leaves": LEAVES,
        "permutation_roots_in_Sym3": perm_roots,
        "unitary_root_X": [[complex(z).real, complex(z).imag] for z in x.ravel()],
        "eigenvalues_of_X": [[complex(z).real, complex(z).imag] for z in np.linalg.eigvals(x)],
        "max_unitarity_error": unitarity,
        "opnorm_of_w0(X)-I": opnorm_defect,
        "root_in_U(O_2)": "T = sum_ij X_ij s_{l_i} s_{l_j}^*, l = (00, 01, 1)",
    }
    json.dump(out, sys.stdout, indent=2)
    print()
    ok = (not perm_roots) and opnorm_defect < 1e-10 and unitarity < 1e-12
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
