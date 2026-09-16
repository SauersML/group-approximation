#!/usr/bin/env python3
"""Checks on the witnesses behind the lower bounds for C_n(F).

1. Exact (sympy) evaluation of the dihedral 2-dimensional family
   U = diag(e^{i a}, e^{-i a}), W = [[0,1],[-1,0]]:
   c = U^2, R1 = U^6, R2 = U^10, so at a = 3 pi / 8
   e(c) = 2 + sqrt2, e(R1) = e(R2) = 2 - sqrt2 and C_2 >= 1 + sqrt2 exactly.
2. A float scan of that family (max over a of the ratio), heuristic only.
3. Numerical commutant dimension of the stored n = 4 and n = 6 witnesses
   (1 means the pair is irreducible), with eigenvalue angles.

Single-threaded; run with `timeout 600`.
"""
import json
import sys

import numpy as np
import sympy as sp

sys.path.insert(0, ".")
from ratio_search import cayley, skew_from_params, words_float, e_float  # noqa: E402


def exact_dihedral():
    a = 3 * sp.pi / 8
    U = sp.diag(sp.exp(sp.I * a), sp.exp(-sp.I * a))
    W = sp.Matrix([[0, 1], [-1, 0]])
    Ui, Wi = U.inv(), W.inv()
    x = U * Wi
    y = Ui * W * U
    z = Ui * Ui * W * U * U
    R1 = x * y * x.inv() * y.inv()
    R2 = x * z * x.inv() * z.inv()
    c = U * W * Ui * Wi
    assert sp.simplify(c - U**2) == sp.zeros(2)
    assert sp.simplify(R1 - U**6) == sp.zeros(2)
    assert sp.simplify(R2 - U**10) == sp.zeros(2)

    def e(g):
        return sp.nsimplify(sp.simplify(2 - sp.re(g.trace())))

    ec, e1, e2 = e(c), e(R1), e(R2)
    ratio_sq = sp.nsimplify(sp.simplify(ec / e1))
    return {"e_c": str(ec), "e_R1": str(e1), "e_R2": str(e2), "ratio_sq": str(ratio_sq),
            "ratio_sq_minus_(1+sqrt2)^2": str(sp.simplify(ratio_sq - (1 + sp.sqrt(2))**2))}


def scan_family(steps=200000):
    a = np.linspace(1e-6, np.pi - 1e-6, steps)
    r = np.abs(np.sin(a)) / np.maximum(np.abs(np.sin(3 * a)), np.abs(np.sin(5 * a)))
    i = int(np.argmax(r))
    return {"max_ratio": float(r[i]), "argmax_over_pi": float(a[i] / np.pi)}


def commutant(fn, n):
    d = json.load(open(fn))
    out = []
    for row in d["rows"]:
        p = np.array(row["params"]) / row["cayley_params_rounded_den"]
        m = n * n
        U = cayley(skew_from_params(p[:m], n))
        W = cayley(skew_from_params(p[m:], n))
        eye = np.eye(n)
        A = np.vstack([np.kron(eye, U) - np.kron(U.T, eye), np.kron(eye, W) - np.kron(W.T, eye)])
        sv = np.sort(np.linalg.svd(A, compute_uv=False))
        R1, R2, c = words_float(U, W)
        out.append({
            "n": n, "tau": row["tau"],
            "smallest_singular_values": [float(v) for v in sv[:4]],
            "commutant_dim_tol_1e-6": int(np.sum(sv < 1e-6)),
            "eig_angles_over_pi_c": [round(float(v), 4) for v in np.sort(np.angle(np.linalg.eigvals(c))) / np.pi],
            "e_c": e_float(c), "e_R1": e_float(R1), "e_R2": e_float(R2),
        })
    return out


if __name__ == "__main__":
    res = {"exact_dihedral_n2": exact_dihedral(), "dihedral_family_scan": scan_family(),
           "witnesses": commutant("ratio_search_n4.json", 4) + commutant("ratio_search_n6.json", 6)}
    print(json.dumps(res, indent=1))
