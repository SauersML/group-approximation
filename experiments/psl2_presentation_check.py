#!/usr/bin/env python3
"""Verify the corrected finite presentation of PSL_2(Z[1/2]) and diagnose the parabolic spectrum.

PSL_2(Z[1/2]) = SL_2(Z) *_{B_+ = B_-} SL_2(Z)  (Serre), B_+ = Gamma_0(2) (lower-left even),
Bbar = <U, w> = Z * C_2 with U = xy = [[1,1],[0,1]] and w = xy^2 xy x = [[1,-1],[2,-1]] (order 2).
sigma = conj by diag(sqrt2,1/sqrt2): sigma(U) = U^2, sigma(w) = w' (order 2 in B_-).
So the amalgam relations are
    x^2 = y^3 = x'^2 = y'^3 = 1,
    xy = (x'y')^2,                         (T = T'^2)
    xy^2 xy x = x'y'^2 x'y' x'.            (w = w')
Check: (a) w has order 2 in the standard rep; (b) the congruence tuple satisfies all relations;
(c) does an autograd search of the CORRECTED presentation still find exact far-from-atomic
solutions?  If exact solutions have atomic (odd-root-of-unity) parabolic spectrum, the
presentation is right and CSP holds; report the eigenvalue phases of T = xy for the best
low-defect solution.
"""

from __future__ import annotations

import json
import math
import sys

import numpy as np


def perm_rep_P1(p):
    pts = [(1, x % p) for x in range(p)] + [(0, 1)]
    index = {pt: i for i, pt in enumerate(pts)}

    def nrm(a, b):
        a %= p; b %= p
        if a != 0:
            inv = pow(a, -1, p); return (1, (b * inv) % p)
        return (0, 1)

    def rho(g):
        d = len(pts); M = np.zeros((d, d))
        for (a, b), i in index.items():
            a2 = (g[0][0] * a + g[0][1] * b) % p
            b2 = (g[1][0] * a + g[1][1] * b) % p
            M[index[nrm(a2, b2)], i] = 1.0
        return M
    return rho, len(pts)


def matmul(*Ms):
    R = Ms[0]
    for M in Ms[1:]:
        R = R @ M
    return R


def hs(A):
    return float(np.sqrt(np.real(np.trace(A.conj().T @ A)) / A.shape[0]))


def check_congruence(p):
    rho, d = perm_rep_P1(p)
    inv2 = pow(2, -1, p)
    S = [[0, -1], [1, 0]]
    ST = [[0, -1], [1, 1]]
    tSt = [[0, (-inv2) % p], [2, 0]]     # t^-1 S t
    tSTt = [[0, (-inv2) % p], [2, 1]]    # t^-1 ST t
    x, y, xp, yp = rho(S), rho(ST), rho(tSt), rho(tSTt)
    I = np.eye(d)
    # w as a matrix in the standard rep to confirm the word
    Smat = np.array([[0, -1.0], [1, 0]])
    STmat = np.array([[0, -1.0], [1, 1]])
    w_std = matmul(Smat, STmat, STmat, Smat, STmat, Smat)  # x y^2 x y x
    r_ord2 = float(np.linalg.norm(w_std @ w_std - np.eye(2)))  # in SL2: w^2 = -I, so ||w^2 - I|| = ||-2I||
    r_ord2_psl = float(np.linalg.norm(w_std @ w_std + np.eye(2)))  # w^2 = -I check
    # relations
    T = x @ y
    Tp = xp @ yp
    rel_T = hs(T - Tp @ Tp)
    w1 = matmul(x, y, y, x, y, x)
    w2 = matmul(xp, yp, xp, yp, yp, xp)  # x' y' x' y'^2 x' (mirror = sigma(w))
    rel_w = hs(w1 - w2)
    orders = [hs(x @ x - I), hs(matmul(y, y, y) - I), hs(xp @ xp - I), hs(matmul(yp, yp, yp) - I)]
    # parabolic order in the congruence rep
    P = I.copy(); ordT = None
    for m in range(1, 4 * d + 2):
        P = P @ T
        if hs(P - I) < 1e-9:
            ordT = m; break
    return {"p": p, "d": d, "w_std_is_order2_psl(||w^2+I||)": r_ord2_psl,
            "rel_T=T'^2": rel_T, "rel_w=w'": rel_w, "orders": orders, "parabolic_order": ordT}


def main():
    out = []
    for p in (3, 5, 7, 11, 13, 17, 23):
        r = check_congruence(p)
        out.append(r)
        print(json.dumps(r))
        sys.stdout.flush()
    with open("experiments/psl2-presentation-check.json", "w") as fh:
        json.dump(out, fh, indent=1)
    print("DONE-SENTINEL")


if __name__ == "__main__":
    main()
