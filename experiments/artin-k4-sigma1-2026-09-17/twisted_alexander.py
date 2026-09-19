#!/usr/bin/env python3
"""Twisted Alexander ranks for A_K, K = K4 with labels u1u2:2, v1v2:2,
u1v1:4, u2v1:4, u2v2:4, u1v2:6, and chi = (1,1,-1,-1).

Criterion (Shapiro + Novikov): for any representation rho: A_K -> GL_d(F),
H_1(A_K; F[t^+-1]^d twisted by rho(g) t^chi(g)) = H_1(ker chi; F^d).
If ker chi is f.g. this is finite-dimensional over F, hence F[t^+-1]-torsion,
so the Fox matrix has rank exactly 4d - rank(d1) = 3d over F(t).
So rank_F(t)(Fox) < 3d  ==>  ker chi is not f.g.  ==>  [chi] not in Sigma^1
(the label-preserving swap u1<->v2, u2<->v1 sends chi to -chi).

Ranks are computed mod a prime p at points t0 in F_p.
"""
import itertools, random, sys, json
import numpy as np

P = 1000003  # prime; entries < 2^20 so int64 matmul is exact for d < 10^6
U1, U2, V1, V2 = 0, 1, 2, 3
CHI = [1, 1, -1, -1]


def inv(w):
    return [(g, -e) for (g, e) in reversed(w)]


def word(s):
    # s like "u1 v1 U1" : lowercase = +1, uppercase = -1
    m = {'u1': U1, 'u2': U2, 'v1': V1, 'v2': V2}
    out = []
    for tok in s.split():
        out.append((m[tok.lower()], 1 if tok[0].islower() else -1))
    return out


def braid(a, b, m):
    """relator prod(a,b;m) prod(b,a;m)^-1"""
    x = []
    y = []
    for k in range(m):
        x.append((a, 1) if k % 2 == 0 else (b, 1))
        y.append((b, 1) if k % 2 == 0 else (a, 1))
    return x + inv(y)


# cross labels (u1v1, u2v1, u2v2, u1v2); override with env K4_LABELS=4,6,4,6 for controls
import os
_L = [int(s) for s in os.environ.get("K4_LABELS", "4,4,4,6").split(",")]
RELS = [braid(U1, U2, 2), braid(V1, V2, 2), braid(U1, V1, _L[0]),
        braid(U2, V1, _L[1]), braid(U2, V2, _L[2]), braid(U1, V2, _L[3])]


def rank_mod_p(M, p=P):
    M = np.array(M, dtype=np.int64) % p
    rows, cols = M.shape
    r = 0
    for c in range(cols):
        if r == rows:
            break
        piv = np.nonzero(M[r:, c])[0]
        if len(piv) == 0:
            continue
        i = r + piv[0]
        if i != r:
            M[[r, i]] = M[[i, r]]
        invp = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * invp) % p
        col = M[:, c].copy()
        col[r] = 0
        nz = np.nonzero(col)[0]
        if len(nz):
            M[nz] = (M[nz] - np.outer(col[nz], M[r]) % p) % p
        r += 1
    return r


def fox_matrix(gens, t0, p=P):
    """gens: list of 4 dxd integer matrices (images rho(x_i)), t0 in F_p.
    Returns (6d x 4d) matrix of Phi(d r_j / d x_i) and the d1 column."""
    d = gens[0].shape[0]
    tinv = pow(t0, p - 2, p)
    Phi = []
    Phiinv = []
    for i, g in enumerate(gens):
        s = t0 if CHI[i] == 1 else tinv
        si = tinv if CHI[i] == 1 else t0
        Phi.append((g.astype(np.int64) * s) % p)
        Phiinv.append(None)
    # inverses mod p via generic modular inverse
    for i, g in enumerate(gens):
        Phiinv[i] = mat_inv_mod(Phi[i], p)
    J = np.zeros((6 * d, 4 * d), dtype=np.int64)
    I = np.eye(d, dtype=np.int64)
    for j, r in enumerate(RELS):
        pref = I.copy()
        for (g, e) in r:
            if e == 1:
                blk = J[j*d:(j+1)*d, g*d:(g+1)*d]
                J[j*d:(j+1)*d, g*d:(g+1)*d] = (blk + pref) % p
                pref = matmul(pref, Phi[g], p)
            else:
                pref = matmul(pref, Phiinv[g], p)
                blk = J[j*d:(j+1)*d, g*d:(g+1)*d]
                J[j*d:(j+1)*d, g*d:(g+1)*d] = (blk - pref) % p
        # sanity: Phi(r) must be identity
        assert np.array_equal(pref % p, I), "relator not satisfied"
    D1 = np.vstack([(Phi[i] - I) % p for i in range(4)])
    return J, D1


def matmul(A, B, p=P):
    return (A % p) @ (B % p) % p


def mat_inv_mod(A, p=P):
    d = A.shape[0]
    M = np.hstack([A % p, np.eye(d, dtype=np.int64)])
    for c in range(d):
        piv = np.nonzero(M[c:, c])[0]
        i = c + piv[0]
        if i != c:
            M[[c, i]] = M[[i, c]]
        iv = pow(int(M[c, c]), p - 2, p)
        M[c] = (M[c] * iv) % p
        col = M[:, c].copy()
        col[c] = 0
        for k in np.nonzero(col)[0]:
            M[k] = (M[k] - int(col[k]) * M[c]) % p
    return M[:, d:]


def twisted_defect(gens, trials=3, p=P, seed=1):
    """Return (max rank of Fox matrix over sampled t, 3d, rank d1)."""
    rng = random.Random(seed)
    d = gens[0].shape[0]
    best = -1
    bd1 = -1
    for _ in range(trials):
        t0 = rng.randrange(2, p - 1)
        J, D1 = fox_matrix(gens, t0, p)
        best = max(best, rank_mod_p(J, p))
        bd1 = max(bd1, rank_mod_p(D1, p))
    return best, 3 * d, bd1
