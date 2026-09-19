#!/usr/bin/env python3
"""Linearized Dogon--Vigdorovich question: uniform gap of the Mayer--Vietoris mismatch map.

SL_2(Z[1/2]) = V_1 *_B V_2 with V_1 = <u, v> = SL_2(Z), V_2 = <u', w> = SL_2(Z)^t,
u = [[1,1],[0,1]], v = [[1,0],[1,1]], u' = u^2, w = [[1,0],[1/2,1]], B = <u^2, v, -I>,
identification:  u^2 (in V_1) = u' (in V_2),   v (in V_1) = w^2 (in V_2).

For a congruence representation rho of SL_2(Z[1/2]) (here: permutation representations
of SL_2(F_p), p odd prime), coefficients Ad rho on M_d.  Cocycles on V_i are determined by
their values on the two generators subject to the two relators of SL_2(Z):
    r1 = (u v^-1 u)^4,    r2 = u v^-1 u v u^-1 v   (i.e. u v^-1 u = v^-1 u v^-1).
The mismatch map  Phi(c_1, c_2) = ( c_1(u^2) - c_2(u'),  c_1(v) - c_2(w^2) ).
Its kernel on Z^1(V_1)+Z^1(V_2) is the set of cocycles of the amalgam, which should be the
diagonal coboundaries {(dx, dx)} (H^1(SL_2(Z[1/2]), Ad rho) = 0 by (T;FD)).
The linearized DV question is whether the smallest nonzero singular value of Phi, with
respect to Hilbert--Schmidt norms on cochains, is bounded below uniformly in p and rho.

Output per (p, rep): d, dim Z^1(V_1), dim Z^1(V_2), dim ker Phi, expected d^2 - dim rho(G)',
rank, smallest nonzero singular value, and a few more small singular values.
"""

from __future__ import annotations

import json
import sys

import numpy as np


def sl2_perm_rep_P1(p):
    """Permutation representation of SL_2(F_p) on P^1(F_p) (d = p+1): returns rho(g) for
    g given as an integer matrix, via a function."""
    pts = [(1, x % p) for x in range(p)] + [(0, 1)]  # (1:x) and infinity (0:1)
    index = {pt: i for i, pt in enumerate(pts)}

    def normalize(a, b):
        a %= p
        b %= p
        if a != 0:
            inv = pow(a, -1, p)
            return (1, (b * inv) % p)
        return (0, 1)

    def rho(g):
        # g acts on column vectors (a, b)^T ; points are (a : b) -> we use row (a,b) with g acting by g @ (a,b)
        d = len(pts)
        M = np.zeros((d, d))
        for (a, b), i in index.items():
            a2 = (g[0][0] * a + g[0][1] * b) % p
            b2 = (g[1][0] * a + g[1][1] * b) % p
            j = index[normalize(a2, b2)]
            M[j, i] = 1.0
        return M

    return rho, len(pts)


def sl2_perm_rep_vectors(p):
    """Permutation representation of SL_2(F_p) on F_p^2 \\ {0} (d = p^2 - 1)."""
    vecs = [(a, b) for a in range(p) for b in range(p) if (a, b) != (0, 0)]
    index = {v: i for i, v in enumerate(vecs)}

    def rho(g):
        d = len(vecs)
        M = np.zeros((d, d))
        for (a, b), i in index.items():
            a2 = (g[0][0] * a + g[0][1] * b) % p
            b2 = (g[1][0] * a + g[1][1] * b) % p
            M[index[(a2, b2)], i] = 1.0
        return M

    return rho, len(vecs)


def ad(R):
    """Matrix of X -> R X R^{-1} on vec(X) (column-major), R unitary/orthogonal."""
    Rinv = np.linalg.inv(R)
    return np.kron(Rinv.T, R)  # vec(R X Rinv) = (Rinv^T kron R) vec(X)


def cocycle_word_map(gens_ad, word):
    """Linear map (c(g_1), ..., c(g_k)) -> c(word) for word a list of (gen_index, +-1).
    gens_ad[i] = Ad of generator i.  Returns (d2, k*d2) matrix."""
    k = len(gens_ad)
    d2 = gens_ad[0].shape[0]
    I = np.eye(d2)
    out = np.zeros((d2, k * d2))
    P = I.copy()  # Ad of prefix
    for (gi, e) in word:
        A = gens_ad[gi]
        if e == 1:
            # c(s) contributes P c(s)
            out[:, gi * d2:(gi + 1) * d2] += P
            P = P @ A
        else:
            Ainv = np.linalg.inv(A)
            # c(s^-1) = -Ad(s^-1) c(s)
            out[:, gi * d2:(gi + 1) * d2] += -P @ Ainv
            P = P @ Ainv
    return out


def nullspace(M, tol=1e-9):
    # eigen-decomposition of M^T M is more robust than gesdd on these structured matrices
    G = M.T @ M
    w, V = np.linalg.eigh(G)
    scale = max(1.0, float(w[-1]) if len(w) else 1.0)
    keep = w <= (tol ** 2) * scale * 1e6  # eigenvalues ~ sigma^2
    rank = int((~keep).sum())
    return V[:, keep], rank


def analyze(p, which):
    if which == "P1":
        rho, d = sl2_perm_rep_P1(p)
    else:
        rho, d = sl2_perm_rep_vectors(p)
    inv2 = pow(2, -1, p)
    u = [[1, 1], [0, 1]]
    v = [[1, 0], [1, 1]]
    u2 = [[1, 2], [0, 1]]
    w = [[1, 0], [inv2, 1]]
    Au, Av, Au2, Aw = ad(rho(u)), ad(rho(v)), ad(rho(u2)), ad(rho(w))
    d2 = d * d
    # relators of SL_2(Z) in generators (g0, g1) = (u, v): r1 = (u v^-1 u)^4 ; r2 = u v^-1 u v u^-1 v
    r1 = [(0, 1), (1, -1), (0, 1)] * 4
    r2 = [(0, 1), (1, -1), (0, 1), (1, 1), (0, -1), (1, 1)]
    C1 = np.vstack([cocycle_word_map([Au, Av], r1), cocycle_word_map([Au, Av], r2)])
    C2 = np.vstack([cocycle_word_map([Au2, Aw], r1), cocycle_word_map([Au2, Aw], r2)])
    Z1, _ = nullspace(C1)
    Z2, _ = nullspace(C2)
    I = np.eye(d2)
    # Phi(a,b,a',b') = ((I + Au) a - a',  b - (I + Aw) b')
    Phi = np.zeros((2 * d2, 4 * d2))
    Phi[:d2, 0:d2] = I + Au
    Phi[:d2, 2 * d2:3 * d2] = -I
    Phi[d2:, d2:2 * d2] = I
    Phi[d2:, 3 * d2:4 * d2] = -(I + Aw)
    # restrict to Z1 + Z2
    Zbasis = np.zeros((4 * d2, Z1.shape[1] + Z2.shape[1]))
    Zbasis[0:2 * d2, :Z1.shape[1]] = Z1
    Zbasis[2 * d2:, Z1.shape[1]:] = Z2
    PhiZ = Phi @ Zbasis
    try:
        s = np.linalg.svd(PhiZ, compute_uv=False)
    except np.linalg.LinAlgError:
        w = np.linalg.eigvalsh(PhiZ.T @ PhiZ)
        s = np.sqrt(np.clip(w[::-1], 0, None))
    tol = 1e-8 * max(1.0, s[0])
    rank = int((s > tol).sum())
    kerdim = PhiZ.shape[1] - rank
    # commutant dimension of rho(G) = rho(SL_2(F_p)) : solve [X, rho(g)] = 0 for g in {u, v, w}
    Cm = np.vstack([Au - I, Av - I, Aw - I])
    _, crank = nullspace(Cm)
    comm_dim = d2 - crank
    smallest_nonzero = s[rank - 1]
    tail = s[max(0, rank - 5):rank].tolist()
    # also H^1(V_1) dimension: dim Z1 - (d2 - dim rho(V_1)')
    _, c1rank = nullspace(np.vstack([Au - I, Av - I]))
    h1_V1 = Z1.shape[1] - (d2 - (d2 - c1rank))
    return {"p": p, "rep": which, "d": d, "dimZ1": int(Z1.shape[1]), "dimZ2": int(Z2.shape[1]),
            "dim_kerPhi": int(kerdim), "expected_diag_coboundaries": int(d2 - comm_dim),
            "commutant_dim": int(comm_dim), "rank": rank,
            "sigma_min_nonzero": float(smallest_nonzero), "tail": tail, "h1_V1": int(h1_V1)}


def main():
    results = []
    for p in (41, 43, 47, 53):
        r = analyze(p, "P1")
        results.append(r)
        print(json.dumps(r))
        sys.stdout.flush()
    with open("experiments/iwahori-linearized-gap-3.json", "w") as fh:
        json.dump(results, fh, indent=1)
    print("DONE-SENTINEL")


if __name__ == "__main__":
    main()
