#!/usr/bin/env python3
"""Replay for spectral-gap-no-output-kill-proof (swarm-0917-w5-ugc-algorithms).

Checks, in floats, on random feasible basic-SDP vector configurations:
  E1  s^4 >= 4s - 3 on [-1, 1]
  E2  edge lemma <N(u), N(v)> >= 1 - 4 eps_e
  M1  deficit identity (exact up to rounding)
  M2  mass outside dom tau <= 4 eta, sum_dom p^2 (1-S) <= 2 eta,
      sum_dom (p - r_tau)^2 <= 8 eta, and the column versions
  R1  exact per-edge failure probability of root rounding
      <= 40 eta_u + 24 eta_v + 14 eps_e  (oriented), hence
      <= 32 eta_u + 32 eta_v + 14 eps_e  (orientation average)
  G1  Dirichlet identity E(N) = (1/2) E_e ||N(u)-N(v)||^2 <= 4 eps
  G2  ||R||^2 <= 4 eps / gamma and E(PN) <= E(N)
  G3  end-to-end: exact expected value of the grid rounding (averaged over
      random shifts) is >= 1 - [r sqrt(8 eps)/Delta + 96 Delta^2
      + 768 eps/gamma + 14 eps]
Everything is computed from Gram data <u_a, w_c>; no tensor is formed.
"""
import numpy as np

rng = np.random.default_rng(20260917)
TOL = 1e-9


def rand_orth(d, scale):
    a = rng.standard_normal((d, d)) * scale
    q, _ = np.linalg.qr(np.eye(d) + a)
    return q


def vertex_vectors(k, d, pert):
    """u_a = p_a Q e_{pi(a)} with random norms and near-identity Q."""
    p = np.abs(rng.standard_normal(k)) + 0.05 * rng.random(k)
    if rng.random() < 0.3:
        p[rng.integers(k)] = 0.0
    p = p / np.linalg.norm(p)
    Q = rand_orth(d, pert)
    perm = rng.permutation(d)[:k]
    U = (Q[:, perm] * p)  # columns u_a
    return U


def norms_units(U):
    p = np.linalg.norm(U, axis=0)
    Ub = np.zeros_like(U)
    nz = p > 1e-14
    Ub[:, nz] = U[:, nz] / p[nz]
    return p, Ub, nz


def nprod(U, W):
    p, Ub, _ = norms_units(U)
    r, Wb, _ = norms_units(W)
    S = (Ub.T @ Wb) ** 2
    return float(p @ (S ** 2) @ r), p, r, S


def edge_eps(U, V, sigma):
    return 1.0 - float(sum(U[:, a] @ V[:, sigma[a]] for a in range(U.shape[1])))


def tau_of(S):
    t = {}
    for a in range(S.shape[0]):
        cs = np.nonzero(S[a] > 0.5)[0]
        if len(cs):
            t[a] = int(cs[0])
    return t


def check_E1():
    s = np.linspace(-1, 1, 20001)
    assert np.all(s ** 4 - 4 * s + 3 >= -TOL)


def sat_prob(Uu, Uv, Uw, sigma):
    _, _, r, Su = nprod(Uu, Uw)
    _, _, _, Sv = nprod(Uv, Uw)
    tu, tv = tau_of(Su), tau_of(Sv)
    iu = {c: a for a, c in tu.items()}
    iv = {c: b for b, c in tv.items()}
    P = 0.0
    for c in range(len(r)):
        if c in iu and c in iv and iv[c] == sigma[iu[c]]:
            P += r[c] ** 2
    return P


def perturb(U0, pert, normnoise, zero_prob=0.2):
    d, k = U0.shape
    p0 = np.linalg.norm(U0, axis=0)
    p = np.abs(p0 * (1 + normnoise * rng.standard_normal(k)))
    if rng.random() < zero_prob:
        p[rng.integers(k)] = 0.0
    p = p / np.linalg.norm(p)
    _, Ub, _ = norms_units(U0)
    Q = rand_orth(d, pert)
    q, _ = np.linalg.qr(Q @ Ub)  # orthonormal columns near Q ubar
    q = q * np.sign(np.diag(q.T @ (Q @ Ub)) + 1e-300)
    return q[:, :k] * p


def base_config(k, d):
    p = np.abs(rng.standard_normal(k)) + 0.05
    p = p / np.linalg.norm(p)
    Q = rand_orth(d, 1.0)
    return Q[:, :k] * p


def feasible(U):
    G = U.T @ U
    off = G - np.diag(np.diag(G))
    return np.abs(off).max() < 1e-9 and abs(np.trace(G) - 1) < 1e-9


def local_trials(T=6000):
    worst = {"E2": 1e9, "M": 1e9, "R1": 1e9, "R1avg": 1e9, "tight": 1e9}
    for _ in range(T):
        k = int(rng.integers(2, 7))
        d = k + int(rng.integers(0, 3))
        pert = float(rng.choice([0.0, 0.01, 0.05, 0.2, 0.6, 2.0]))
        nn = float(rng.choice([0.0, 0.02, 0.1, 0.5]))
        U0 = base_config(k, d)
        sigma = rng.permutation(k)
        inv = np.argsort(sigma)
        Uu = perturb(U0, pert, nn)
        Uw = perturb(U0, pert, nn)[:, rng.permutation(k)]
        Uv = perturb(U0, pert, nn)[:, inv]  # V[:, sigma[a]] ~ U0[:, a]
        if rng.random() < 0.1:
            sigma = rng.permutation(k)
        for U in (Uu, Uv, Uw):
            assert feasible(U)
        nuv = nprod(Uu, Uv)[0]
        e = edge_eps(Uu, Uv, sigma)
        worst["E2"] = min(worst["E2"], nuv - (1 - 4 * e))
        nuw, p, r, S = nprod(Uu, Uw)
        eta = 1 - nuw
        rhs = (0.5 * (p ** 2) @ (1 - (S ** 2).sum(1))
               + 0.5 * (r ** 2) @ (1 - (S ** 2).sum(0))
               + 0.5 * ((p[:, None] - r[None, :]) ** 2 * S ** 2).sum())
        assert abs(eta - rhs) < 1e-9, (eta, rhs)
        t = tau_of(S)
        assert len(set(t.values())) == len(t)
        rg = set(t.values())
        out_p = sum(p[a] ** 2 for a in range(k) if a not in t)
        out_r = sum(r[c] ** 2 for c in range(k) if c not in rg)
        m1 = sum(p[a] ** 2 * (1 - S[a, t[a]]) for a in t)
        m2 = sum(r[t[a]] ** 2 * (1 - S[a, t[a]]) for a in t)
        m3 = sum((p[a] - r[t[a]]) ** 2 for a in t)
        worst["M"] = min(worst["M"], 4 * eta - out_p, 4 * eta - out_r,
                         2 * eta - m1, 2 * eta - m2, 8 * eta - m3)
        eta_v = 1 - nprod(Uv, Uw)[0]
        P = sat_prob(Uu, Uv, Uw, sigma)
        worst["R1"] = min(worst["R1"], 40 * eta + 24 * eta_v + 14 * e - (1 - P))
        b = 32 * eta + 32 * eta_v + 14 * e
        worst["R1avg"] = min(worst["R1avg"], b - (1 - P))
        if 1 - P > 1e-6:
            worst["tight"] = min(worst["tight"], b / (1 - P))
    return worst


def planted_game(N, k, d, nperm, pert, nn, corrupt):
    """Union of nperm random permutation graphs (an expander w.h.p.), planted
    labels pi_u, vectors = perturbation of one base configuration."""
    U0 = base_config(k, d)
    pis = [rng.permutation(k) for _ in range(N)]
    vecs = [perturb(U0, pert, nn, 0.0)[:, np.argsort(pis[u])] for u in range(N)]
    # vecs[u][:, pis[u][a]] ~ U0[:, a]
    edges = []
    for _ in range(nperm):
        perm = rng.permutation(N)
        for u in range(N):
            v = int(perm[u])
            if v == u:
                continue
            sigma = pis[v][np.argsort(pis[u])]  # u-label pi_u(a) -> pi_v(a)
            if rng.random() < corrupt:
                sigma = rng.permutation(k)
            edges.append((u, v, 1, sigma))
    return vecs, edges


def global_trial(N=40, k=4, d=5, nperm=3, pert=0.03, nn=0.03, corrupt=0.01,
                 shifts=40):
    vecs, edges = planted_game(N, k, d, nperm, pert, nn, corrupt)
    W = sum(w for (_, _, w, _) in edges)
    Wm = np.zeros((N, N))
    for (u, v, w, _) in edges:
        Wm[u, v] += w
        Wm[v, u] += w
    deg = Wm.sum(1)
    pi = deg / (2 * W)
    eps_e = np.array([edge_eps(vecs[u], vecs[v], s) for (u, v, _, s) in edges])
    wts = np.array([w for (_, _, w, _) in edges]) / W
    eps = float(wts @ eps_e)
    G = np.array([[nprod(vecs[u], vecs[w])[0] for w in range(N)]
                  for u in range(N)])
    Dir = 0.5 * sum(wt * (2 - 2 * G[u, v]) for wt, (u, v, _, _) in zip(wts, edges))
    Dir2 = 0.5 * float(pi @ (Wm / deg[:, None] * (2 * np.diag(G)[:, None]
                                                  - 2 * G)).sum(1))
    assert abs(Dir - Dir2) < 1e-9 and Dir <= 4 * eps + 1e-9
    Ds = np.diag(deg ** -0.5)
    lam, phi = np.linalg.eigh(Ds @ Wm @ Ds)
    order = np.argsort(-lam)
    lam, phi = lam[order], phi[:, order]
    H = phi / np.sqrt(pi)[:, None]  # h_i(u) = phi_i(u) / sqrt(pi(u))
    out = []
    for m in range(1, 5):
        gamma = 1 - lam[m] if m < N else 1.0
        Hm = H[:, :m]
        Pi = np.diag(pi)
        Cg = Hm.T @ Pi @ G @ Pi @ Hm       # <c_i, c_j>
        NxC = G @ Pi @ Hm                   # <N(u), c_i>
        xx = np.einsum('ui,ij,uj->u', Hm, Cg, Hm)
        Nx = np.einsum('ui,ui->u', Hm, NxC)
        R2 = np.diag(G) - 2 * Nx + xx
        assert float(pi @ R2) <= 4 * eps / gamma + 1e-9
        ev, evec = np.linalg.eigh(Cg)
        L = evec * np.sqrt(np.clip(ev, 0, None))
        X = Hm @ L                          # coordinates of PN(u) in R^m
        # E(PN) <= E(N)
        GX = X @ X.T
        DirP = 0.5 * sum(wt * (GX[u, u] + GX[v, v] - 2 * GX[u, v])
                         for wt, (u, v, _, _) in zip(wts, edges))
        assert DirP <= Dir + 1e-9
        r = m
        A = r * np.sqrt(8 * eps)
        Delta = (A / 192) ** (1 / 3) if m > 1 else 1e-12
        ell = Delta / np.sqrt(m)
        vals = []
        for _ in range(shifts):
            theta = rng.random(m) * ell
            cells = [tuple(np.floor((X[u] - theta) / ell).astype(int))
                     for u in range(N)]
            root = {}
            for u in range(N):
                c = cells[u]
                if c not in root or R2[u] < R2[root[c]]:
                    root[c] = u
            val = 0.0
            for wt, (u, v, _, s) in zip(wts, edges):
                if cells[u] != cells[v]:
                    continue
                wr = root[cells[u]]
                val += wt * sat_prob(vecs[u], vecs[v], vecs[wr], s)
            vals.append(val)
        Ev = float(np.mean(vals))
        sep = A / Delta if m > 1 else 0.0
        bound = sep + (96 * Delta ** 2 if m > 1 else 0.0) \
            + 768 * eps / gamma + 14 * eps
        out.append((m, gamma, eps, Ev, 1 - bound))
    return out


def main():
    check_E1()
    w = local_trials()
    print("local worst slacks:", {k: round(v, 6) for k, v in w.items()})
    assert w["E2"] >= -TOL and w["M"] >= -TOL
    assert w["R1"] >= -TOL and w["R1avg"] >= -TOL
    for params in [dict(), dict(pert=0.005, nn=0.005, corrupt=0.002),
                   dict(N=60, nperm=4, pert=0.0005, nn=0.0005, corrupt=0.0),
                   dict(N=60, nperm=5, pert=0.00003, nn=0.00003, corrupt=0.0)]:
        for (m, gamma, eps, Ev, lb) in global_trial(**params):
            print(f"m={m} gamma={gamma:.3f} eps={eps:.5f} "
                  f"E[val]={Ev:.4f} bound={lb:.4f}")
            assert Ev >= lb - 1e-9
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()


