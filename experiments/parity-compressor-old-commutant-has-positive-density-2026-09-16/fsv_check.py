#!/usr/bin/env python3
"""Finite checks for the finitary-mark right-supported averaging bound.

For a finite group F acting unitarily on C^d, put
    T   = (1/|F|) sum_k rho(k) (x) conj(rho(k))    (adjoint averaging)
    R_Z = I (x) conj(Z),   Z=(1-rho(J))/2,  J in F an involution.
The note proves
    ||T R_Z||_2^2 = (1/|F|) sum_k tr(k) tr(Z k)                    (FSV-a)
                  = sum_sigma a_sigma tr(Z p_sigma)/n_sigma^2
                 <= tr(P_F) tr(Z P_F) + tr(Z)/delta(F)^2            (FSV-b)
with tr(Z P_F)=0 because J in F, and the exact F-commutant right-supported
on Z is zero when J is not central (FSV-c).  It also checks the averaging
identity
    (1/L^2) sum_ij ||(V_i-V_j)P||_2^2 = 2 tr(P) - 2 ||T P||_2^2     (FSV-d)
for a random adjoint projection P.  All traces are normalized (tr I = 1 on
C^d and tr_ad I = 1 on End(C^d)).

F = GL_n(F_2), n=3,4, acting by permutations of nonzero vectors plus
hyperplanes (d = 2(2^n-1)).  delta(GL_3(2))=3, delta(GL_4(2))=7 are the
classical minimal nontrivial degrees (PSL_3(2) and A_8); the script only
uses them in the printed comparison (FSV-b).
Single-threaded, a few seconds.
"""
import itertools
import numpy as np

rng = np.random.default_rng(20260916)


def gl2(n):
    elems = []
    for bits in itertools.product((0, 1), repeat=n * n):
        m = np.array(bits, dtype=np.int64).reshape(n, n)
        # rank over F_2 by elimination
        a = m.copy()
        r = 0
        for c in range(n):
            piv = None
            for i in range(r, n):
                if a[i, c]:
                    piv = i
                    break
            if piv is None:
                continue
            a[[r, piv]] = a[[piv, r]]
            for i in range(n):
                if i != r and a[i, c]:
                    a[i] ^= a[r]
            r += 1
        if r == n:
            elems.append(m)
    return elems


def perm_rep(elems, n):
    vecs = [np.array(v, dtype=np.int64) for v in itertools.product((0, 1), repeat=n) if any(v)]
    idx = {tuple(v): i for i, v in enumerate(vecs)}
    N = len(vecs)
    mats = []
    for g in elems:
        # action on vectors: v -> g v ; action on hyperplanes {x: w.x=0}: w -> g^{-T} w
        ginvT = None
        # inverse over F_2 by brute force search within the group is slow; use adjugate mod 2
        det = int(round(np.linalg.det(g))) % 2
        assert det == 1
        adj = np.round(np.linalg.inv(g) * np.linalg.det(g)).astype(np.int64) % 2
        ginvT = adj.T % 2
        P = np.zeros((2 * N, 2 * N))
        for i, v in enumerate(vecs):
            P[idx[tuple((g @ v) % 2)], i] = 1.0
            P[N + idx[tuple((ginvT @ v) % 2)], N + i] = 1.0
        mats.append(P)
    return mats


def transvection(n):
    t = np.eye(n, dtype=np.int64)
    t[0, 1] = 1
    return t


def run(n, delta, build_adjoint):
    elems = gl2(n)
    mats = perm_rep(elems, n)
    d = mats[0].shape[0]
    Fsize = len(elems)
    tJ = transvection(n)
    jpos = [i for i, g in enumerate(elems) if np.array_equal(g, tJ)][0]
    J = mats[jpos]
    Z = (np.eye(d) - J) / 2.0
    tr = lambda A: np.trace(A) / A.shape[0]
    PF = sum(mats) / Fsize
    trk = np.array([tr(M) for M in mats])
    trZk = np.array([tr(Z @ M) for M in mats])
    formula = float(np.mean(trk * trZk))
    bound = tr(PF) * tr(Z @ PF) + tr(Z) / delta ** 2
    print(f"GL_{n}(F_2): |F|={Fsize}, d={d}, tr(Z)={tr(Z):.6f}, tr(P_F)={tr(PF):.6f}, "
          f"tr(Z P_F)={tr(Z @ PF):.3e}")
    print(f"  (FSV-a) trace formula ||T R_Z||_2^2 = {formula:.8f}")
    print(f"  (FSV-b) bound tr(P_F)tr(ZP_F)+tr(Z)/delta^2 = {bound:.8f}  holds={formula <= bound + 1e-12}")
    unrestricted = float(np.mean(trk * trk))
    print(f"  unrestricted ||T||_2^2 = {unrestricted:.8f}  vs tr(P_F)^2+1/delta^2 = {tr(PF)**2 + 1/delta**2:.8f}")
    if not build_adjoint:
        return
    D = d * d
    T = np.zeros((D, D))
    for M in mats:
        T += np.kron(M, M)  # real matrices: conj = itself
    T /= Fsize
    RZ = np.kron(np.eye(d), Z)
    TRZ = T @ RZ
    hs = float(np.sum(TRZ * TRZ) / D)
    print(f"  (FSV-a) direct ||T R_Z||_2^2 = {hs:.8f}  agree={abs(hs - formula) < 1e-10}")
    W = T @ RZ @ T
    ev = np.linalg.eigvalsh((W + W.T) / 2)
    dim_int = int(np.sum(ev > 1 - 1e-9))
    print(f"  (FSV-c) dim(F-commutant right-supported on Z) = {dim_int}; rank T = {int(round(np.trace(T)))}")
    # (FSV-d) averaging identity for a random rank-r adjoint projection
    r = 7
    Q, _ = np.linalg.qr(rng.standard_normal((D, r)))
    P = Q @ Q.T
    trP = r / D
    lhs = 0.0
    V = [np.kron(M, M) for M in mats[:60]]  # a 60-element subset g_1..g_L
    L = len(V)
    Tsub = sum(V) / L
    for Vi in V:
        for Vj in V:
            X = (Vi - Vj) @ Q
            lhs += np.sum(X * X) / D
    lhs /= L * L
    rhs = 2 * trP - 2 * float(np.sum((Tsub @ Q) ** 2) / D)
    print(f"  (FSV-d) identity: lhs={lhs:.10f} rhs={rhs:.10f} agree={abs(lhs - rhs) < 1e-10}")


if __name__ == "__main__":
    run(3, 3, build_adjoint=True)
    run(4, 7, build_adjoint=False)
