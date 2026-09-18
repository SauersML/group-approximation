#!/usr/bin/env python3
"""Coprime affine extensions of the U_4(F_p) image of Gamma_p (2026-09-17).

Gamma_p = HC1 KMS group (see kmslib).  G0 = U_4(F_p), rho0(a)=x12, rho0(b)=x23,
rho0(c)=x34 (all HC1 relators hold: <a,b>,<b,c> Heisenberg, [a,c]=1).
rho0(w_p)=1.

Criterion (coprime cochain complex of the triangle of groups, l != p):
for an F_l G0-module M, Z^1(Gamma_p;M) = {(m_ab,m_bc,m_ac)} with pairwise
differences fixed by the edge generators.  With m_ac=0:
   x in M^a, y in M^c, x-y in M^b,
and the affine lift a->(A,0), c->(C,0), b->(B,(B-I)x) is a representation
of Gamma_p (each vertex group is conjugate to its linear image by a translation).
Its value on w_p is the translation N_g (R-I)(x-y), g=rho(rs).

Modules: M = Ind_A^{G0} chi, A = {[[I,X],[0,I]]} (abelian normal, index p^2),
chi ranging over all p^4 characters of A with values in F_l (l = 1 mod p).
Every irreducible F_l G0-module is a constituent of one of these.
Usage: coprime_u4.py <p> <l1,l2,...>
"""
import itertools
import sys

import numpy as np

sys.path.insert(0, "/home/user/group-approximation/experiments/kms-hc1-root-word-finite-images-2026-09-16")
import kmslib as K  # noqa: E402

p = int(sys.argv[1])
ells = [int(x) for x in sys.argv[2].split(",")]


def E(i, j, e=1):
    M = np.eye(4, dtype=np.int64)
    M[i, j] = e % p
    return M


def t(i, j):
    return (E(0, 1, i) @ E(2, 3, j)) % p


def tinv(i, j):
    return (E(2, 3, -j) @ E(0, 1, -i)) % p


cosets = [(i, j) for i in range(p) for j in range(p)]
idx = {cs: k for k, cs in enumerate(cosets)}


def mono_data(g):
    """For g in U_4(F_p): list of (target coset index, A-coordinates) per source coset."""
    out = []
    for (i, j) in cosets:
        h = (g @ t(i, j)) % p
        i2, j2 = int(h[0, 1]), int(h[2, 3])
        al = (tinv(i2, j2) @ h) % p
        assert al[0, 1] == 0 and al[2, 3] == 0
        out.append((idx[(i2, j2)], (int(al[0, 2]), int(al[0, 3]), int(al[1, 2]), int(al[1, 3]))))
    return out


gens = [E(0, 1), E(1, 2), E(2, 3)]
data = [mono_data(g) for g in gens]
n = p * p


def rep_mats(chi, l, zeta):
    mats = []
    for dat in data:
        M = np.zeros((n, n), dtype=np.int64)
        for src, (tgt, al) in enumerate(dat):
            ex = sum(c * x for c, x in zip(chi, al)) % p
            M[tgt, src] = pow(zeta, ex, l)
        mats.append(M)
    return mats


def detect(mats, l):
    A, B, C = mats
    I = np.eye(n, dtype=np.int64)
    Ai, Bi, Ci = (K.mat_inv_mod(X, l) for X in mats)
    R = (Bi @ Ai @ B @ A) % l
    S = (Bi @ Ci @ B @ C) % l
    G = (R @ S) % l
    Na = K.rref_nullspace((A - I) % l, l)
    Nc = K.rref_nullspace((C - I) % l, l)
    Mb = np.concatenate([((B - I) @ Na) % l, (-(B - I) @ Nc) % l], axis=1)
    lam = K.rref_nullspace(Mb, l)
    if lam.shape[1] == 0:
        return 0, None
    X = (Na @ lam[:Na.shape[1]]) % l
    Y = (Nc @ lam[Na.shape[1]:]) % l
    U = (X - Y) % l
    Ng = np.zeros((n, n), dtype=np.int64)
    P = I.copy()
    for _ in range(p):
        Ng = (Ng + P) % l
        P = (P @ G) % l
    img = (Ng @ ((R - I) @ U)) % l
    rk = K.rank_mod(img, l)
    if rk == 0:
        return 0, None
    # pick a column with nonzero image
    col = int(np.nonzero(img.any(axis=0))[0][0])
    return rk, X[:, col]


def verify(mats, l, x):
    A, B, C = mats
    I = np.eye(n, dtype=np.int64)
    def aff(M, v):
        W = np.zeros((n + 1, n + 1), dtype=np.int64)
        W[:n, :n] = M
        W[:n, n] = v % l
        W[n, n] = 1
        return W
    zero = np.zeros(n, dtype=np.int64)
    rep = K.Rep([aff(A, zero), aff(B, ((B - I) @ x) % l), aff(C, zero)], l)
    rel = rep.check_relators(p)
    wI = rep.is_identity(K.root_word(p))
    return all(rel.values()), wI


for l in ells:
    assert (l - 1) % p == 0
    # primitive p-th root of unity mod l
    zeta = next(z for z in range(2, l) if pow(z, p, l) == 1 and z != 1)
    found = 0
    tested = 0
    for chi in itertools.product(range(p), repeat=4):
        mats = rep_mats(chi, l, zeta)
        tested += 1
        rk, x = detect(mats, l)
        if rk:
            ok, wI = verify(mats, l, x)
            print(f"p={p} l={l} chi={chi}: rank(delta->delta(w))={rk} relators_ok={ok} affine w=I:{wI}", flush=True)
            found += 1
            if found >= 3:
                break
    print(f"p={p} l={l}: tested {tested} characters, detecting modules found: {found}", flush=True)
