#!/usr/bin/env python3
"""Z/4-equivariant one-unitary search for Higman operator-norm microstates.

Lossless reduction (see research/higman-opnorm-collapse-is-a-one-unitary-z4-problem.md):
every tuple (U_0..U_3) in U(L)^4 with defect delta amplifies to
P = diag(U_0,U_1,U_2,U_3) in U(4L), S = block shift of order four, with
S^i P S^-i = diag(U_i,...,U_(i+3)), all four relators unitarily equivalent to
    E(P) = P Q P^* - Q^2,     Q = S P S^*,
and ||P-1|| = max_i ||U_i-1||.  Conversely every P gives the tuple U_i=S^iPS^-i.
So the collapse modulus is the one-unitary problem  inf ||E(P)||  over far P.

Search: Riemannian descent on the smooth max F_beta=(1/beta) log sum_k exp(beta
sigma_k(E)) with continuation beta = 10..3000 (Armijo steps), then the bundle
minimax polish of minimax_polish.py specialised to one relator.

Usage:
  python3 equivariant_search.py amp                 amplify+polish the L=12 witness (N=48)
  python3 equivariant_search.py rand N starts seed  random P in U(N), N divisible by 4
  python3 equivariant_search.py pad P.npy k eps     pad each grade block of a saved P by k
                                                    identity rows, perturb by eps, descend
Saved P: set SAVE_TUPLE=path.npy.
"""
import os
import sys
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from minimax_polish import load_witness, haar, op, skew  # noqa: E402


def block_shift(N):
    m = N // 4
    S = np.zeros((N, N))
    for j in range(4):
        # block j+1 -> block j, so S diag(A0,A1,A2,A3) S^* = diag(A1,A2,A3,A0)
        S[j * m:(j + 1) * m, ((j + 1) % 4) * m:((j + 2) % 4) * m or N] = np.eye(m)
    return S


def relator(P, S):
    Q = S @ P @ S.T
    return P @ Q @ P.conj().T - Q @ Q


def grad_triple(P, S, u, v):
    Q = S @ P @ S.T
    W = np.outer(v, u.conj())
    Ph = P.conj().T
    M = (Q @ Ph @ W @ P + S.T @ Ph @ W @ P @ S @ P - Ph @ W @ P @ Q
         - S.T @ Q @ W @ S @ P - S.T @ W @ Q @ S @ P)
    return skew(M.conj().T)


def smooth(P, S, beta):
    E = relator(P, S)
    Us, s, Vh = np.linalg.svd(E)
    z = beta * (s - s[0])
    w = np.exp(z)
    F = s[0] + np.log(w.sum()) / beta
    w /= w.sum()
    G = sum(w[k] * grad_triple(P, S, Us[:, k], Vh[k].conj()) for k in range(len(s)) if w[k] > 1e-12)
    return F, G, s[0]


def descend(P, S, beta, iters):
    F, G, d = smooth(P, S, beta)
    step = 0.05
    for it in range(iters):
        nrm = np.linalg.norm(G)
        if nrm < 1e-12:
            break
        while step > 1e-12:
            Pn = P @ expm(-step * G / nrm)
            Fn, Gn, dn = smooth(Pn, S, beta)
            if Fn < F - 1e-4 * step * nrm:
                P, F, G, d = Pn, Fn, Gn, dn
                step *= 1.4
                break
            step /= 2
        else:
            break
    return P, d


def polish(P, S, iters=400, tau=0.02, rho=0.2):
    d = op(relator(P, S))
    for it in range(iters):
        E = relator(P, S)
        Us, s, Vh = np.linalg.svd(E)
        idx = [k for k in range(min(12, len(s))) if s[k] >= s[0] - tau]
        sig = s[idx]
        Gs = [grad_triple(P, S, Us[:, k], Vh[k].conj()) for k in idx]
        Gm = np.array([np.concatenate([g.real.ravel(), g.imag.ravel()]) for g in Gs])
        Qm = Gm @ Gm.T
        n = len(idx)
        accepted = False
        while rho > 1e-10:
            res = minimize(lambda l: 0.5 * rho * l @ Qm @ l - l @ sig, np.ones(n) / n,
                           jac=lambda l: rho * Qm @ l - sig, method="SLSQP", bounds=[(0, 1)] * n,
                           constraints=[{"type": "eq", "fun": lambda l: l.sum() - 1}], options={"maxiter": 100})
            lam = np.clip(res.x, 0, None)
            lam /= lam.sum()
            X = -rho * sum(lam[k] * Gs[k] for k in range(n))
            Pn = P @ expm(X)
            dn = op(relator(Pn, S))
            if dn < d - 1e-12:
                P, d, rho, accepted = Pn, dn, min(rho * 1.5, 2.0), True
                break
            rho /= 2
        if not accepted:
            tau /= 2
            rho = 0.2
            if tau < 1e-8:
                break
    return P, d


def run(P, S, tag):
    N = P.shape[0]
    for beta in (10, 30, 100, 300, 1000, 3000):
        P, d = descend(P, S, beta, int(os.environ.get("ITERS", "300")))
        print(f"  {tag} beta={beta}: def={d:.6f}", flush=True)
    P, d = polish(P, S)
    dist = op(P - np.eye(N))
    print(f"{tag} N={N}: polished def={d:.6f} ||P-1||={dist:.4f}", flush=True)
    return P, d, dist


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "amp"
    if mode == "amp":
        U = load_witness()
        L = U[0].shape[0]
        N = 4 * L
        P = np.zeros((N, N), dtype=complex)
        for j in range(4):
            P[j * L:(j + 1) * L, j * L:(j + 1) * L] = U[j]
        S = block_shift(N)
        print("amplified witness def:", op(relator(P, S)))
        rng = np.random.default_rng(3)
        # small off-block perturbation so descent can leave the amplified slice
        H = skew(rng.normal(size=(N, N)) + 1j * rng.normal(size=(N, N)))
        P = P @ expm(0.02 * H / np.linalg.norm(H, 2))
        P, d, dist = run(P, S, "amp")
        if os.environ.get("SAVE_TUPLE"):
            np.save(os.environ["SAVE_TUPLE"], P)
        return
    if mode == "pad":
        # pad each grade block of a saved P by k identity rows, perturb, descend
        P0 = np.load(sys.argv[2])
        k = int(sys.argv[3])
        eps = float(sys.argv[4]) if len(sys.argv) > 4 else 0.05
        m0 = P0.shape[0] // 4
        m = m0 + k
        N = 4 * m
        P = np.eye(N, dtype=complex)
        idx = np.concatenate([np.arange(j * m, j * m + m0) for j in range(4)])
        P[np.ix_(idx, idx)] = P0
        S = block_shift(N)
        print(f"padded N={N} def:", op(relator(P, S)), flush=True)
        rng = np.random.default_rng(5)
        H = skew(rng.normal(size=(N, N)) + 1j * rng.normal(size=(N, N)))
        P = P @ expm(eps * H / np.linalg.norm(H, 2))
        P, d, dist = run(P, S, "pad")
        if os.environ.get("SAVE_TUPLE"):
            np.save(os.environ["SAVE_TUPLE"], P)
        return
    N = int(sys.argv[2])
    starts = int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    rng = np.random.default_rng(seed)
    S = block_shift(N)
    best = 9
    for s in range(starts):
        P, d, dist = run(haar(N, rng), S, f"start{s}")
        if dist > 1.5 and d < best:
            best = d
            if os.environ.get("SAVE_TUPLE"):
                np.save(os.environ["SAVE_TUPLE"], P)
    print(f"BEST far N={N}: {best:.6f}")


if __name__ == "__main__":
    main()
