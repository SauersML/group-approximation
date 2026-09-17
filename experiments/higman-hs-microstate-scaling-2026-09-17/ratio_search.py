#!/usr/bin/env python3
"""Directed search for large HS word-stability ratios of Higman-type cycles.

For relators r_j = g_j g_{j+1} g_j^{-1} g_{j+1}^{-2} (j on a cycle Z/k or a path)
and normalized HS energies e_v = ||v - I||_2^2 = tr((v-I)^*(v-I))/d, put

    ratio(U) = e_{g_0}(U) / sum_j e_{r_j}(U).

C_d(k) = sup over U(d)^k of ratio.  For each fixed d, C_d is finite (the only
exact d-dimensional representation is trivial and the relator map has injective
differential at the identity), and C(k) = sup_d C_d(k) is the best constant in the
marked HS word inequality  e_{g_0} <= C sum_j e_{r_j}.
  * k = 3 (Higman's trivial 3-cycle):  C(3) < infinity (van Kampen area bound).
  * k = 4 (Higman's group):  C(4) < infinity  =>  Hig not hyperlinear;
                             Hig hyperlinear  =>  C(4) = infinity.
We maximize log e_{g_0} - log sum e_r over the full unitary group by Riemannian
nonlinear CG (left-invariant exponential steps), many random restarts.
"""
import argparse, json, time
import numpy as np
from scipy.linalg import expm

def edges(topo, k):
    if topo == "cycle":
        return [(i, (i + 1) % k) for i in range(k)]
    return [(i, i + 1) for i in range(k - 1)]

def objective(g, E):
    """Return J = log(sum e_r) - log(e_0), descent generators S_i, (e0, er list)."""
    d = g[0].shape[0]
    Gr = [np.zeros_like(x) for x in g]
    er = []
    for (i, j) in E:
        a, b = g[i], g[j]
        R = a @ b @ a.conj().T - b @ b          # ||R||_2 = ||r_j - I||_2
        er.append(np.vdot(R, R).real / d)
        Gr[i] += (R @ a @ b.conj().T + R.conj().T @ a @ b) / d
        Gr[j] += (a.conj().T @ R @ a - R @ b.conj().T - b.conj().T @ R) / d
    Er = sum(er)
    e0 = (2 * d - 2 * np.trace(g[0]).real) / d
    G = [x / Er for x in Gr]
    G[0] = G[0] - (-np.eye(d) / d) / e0
    S = []
    for x, Gx in zip(g, G):
        X = x @ Gx.conj().T
        S.append((X - X.conj().T) / 2)        # descent generator: g <- expm(t S) g
    return np.log(Er) - np.log(e0), S, (e0, er)

def step(g, D, t):
    return [expm(t * s) @ x for x, s in zip(g, D)]

def haar(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))

def cg(g, E, iters, tol=1e-13, log_every=0):
    J, S, info = objective(g, E)
    D = [s.copy() for s in S]
    t, hist = 0.1, []
    for it in range(iters):
        n2 = sum(np.vdot(s, s).real for s in S)
        if n2 < tol:
            break
        slope = sum(np.vdot(dd, s).real for dd, s in zip(D, S))
        if slope <= 0:
            D, slope = [s.copy() for s in S], n2
        while True:
            gn = step(g, D, t)
            Jn, Sn, infon = objective(gn, E)
            if Jn <= J - 0.2 * t * 2 * slope or t < 1e-14:
                break
            t *= 0.5
        beta = max(0.0, sum(np.vdot(sn, sn - s).real for sn, s in zip(Sn, S)) / n2)
        D = [sn + beta * dd for sn, dd in zip(Sn, D)]
        g, J, S, info = gn, Jn, Sn, infon
        t = min(2 * t, 10.0)
        if log_every and it % log_every == 0:
            hist.append((it, float(np.exp(-J))))
    return g, J, info, hist, it + 1

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--topo", default="cycle")
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--d", type=int, default=3)
    ap.add_argument("--restarts", type=int, default=10)
    ap.add_argument("--iters", type=int, default=3000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default="")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    E = edges(a.topo, a.k)
    best = None
    for r in range(a.restarts):
        t0 = time.time()
        g = [haar(a.d, rng) for _ in range(a.k)]
        g, J, (e0, er), hist, its = cg(g, E, a.iters)
        rec = dict(topo=a.topo, k=a.k, d=a.d, restart=r, ratio=float(np.exp(-J)),
                   e0=float(e0), er=[float(x) for x in er], iters=its,
                   secs=round(time.time() - t0, 1))
        print(json.dumps(rec), flush=True)
        if best is None or rec["ratio"] > best[0]["ratio"]:
            best = (rec, g)
    if a.out:
        np.savez_compressed(a.out, *best[1])
    print("BEST", json.dumps(best[0]), flush=True)

if __name__ == "__main__":
    main()

def rand_skew(d, rng):
    z = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return (z - z.conj().T) / 2

def grow(k=4, topo="cycle", d0=3, D=16, tries=6, iters=3000, eps=0.3, seed=0, restarts0=16):
    """Monotone growth: best witness in dim d-1, padded by a 1x1 identity block and
    perturbed by expm(eps*random skew), re-optimized; also fresh random starts."""
    rng = np.random.default_rng(seed)
    E = edges(topo, k)
    best_g, best_r = None, -1
    for r in range(restarts0):
        g, J, info, _, _ = cg([haar(d0, rng) for _ in range(k)], E, iters)
        if np.exp(-J) > best_r:
            best_g, best_r = g, float(np.exp(-J))
    out = [dict(d=d0, ratio=best_r)]
    print(json.dumps(dict(topo=topo, k=k, **out[-1])), flush=True)
    for d in range(d0 + 1, D + 1):
        base = []
        for x in best_g:
            y = np.eye(d, dtype=complex); y[:d - 1, :d - 1] = x; base.append(y)
        cand_g, cand_r = base, best_r
        for t in range(tries):
            g0 = [expm(eps * rand_skew(d, rng) / np.sqrt(d)) @ x for x in base]
            g, J, info, _, _ = cg(g0, E, iters)
            if np.exp(-J) > cand_r:
                cand_g, cand_r = g, float(np.exp(-J))
        best_g, best_r = cand_g, cand_r
        J, _, (e0, er) = objective(best_g, E)
        out.append(dict(d=d, ratio=best_r, e0=float(e0), er_sum=float(sum(er))))
        print(json.dumps(dict(topo=topo, k=k, **out[-1])), flush=True)
        np.savez_compressed(f"grow_{topo}{k}_d{d}.npz", *best_g)
    return out

def pad(g, d):
    out = []
    for x in g:
        y = np.eye(d, dtype=complex); y[:x.shape[0], :x.shape[0]] = x; out.append(y)
    return out

def dsum(g, h):
    out = []
    for x, y in zip(g, h):
        a, b = x.shape[0], y.shape[0]
        z = np.zeros((a + b, a + b), dtype=complex); z[:a, :a] = x; z[a:, a:] = y; out.append(z)
    return out

def hop(g, E, rounds, rng, eps_list=(0.2, 0.5, 1.0, 2.0), iters=3000):
    """Basin hopping on U(d)^k: perturb current best by expm(eps * random skew/sqrt d)."""
    d = g[0].shape[0]
    J, _, _ = objective(g, E)
    best_g, best_r = g, float(np.exp(-J))
    log = []
    for r in range(rounds):
        eps = eps_list[r % len(eps_list)]
        g0 = [expm(eps * rand_skew(d, rng) / np.sqrt(d)) @ x for x in best_g]
        gn, Jn, info, _, its = cg(g0, E, iters)
        rn = float(np.exp(-Jn))
        if rn > best_r * (1 + 1e-9):
            best_g, best_r = gn, rn
            log.append((r, eps, rn))
    return best_g, best_r, log

def objective_iso(g, E, iso):
    """Like objective, but generators in `iso` move by conjugation only (spectrum frozen)."""
    J, S, info = objective(g, E)
    d = g[0].shape[0]
    Gr = [np.zeros_like(x) for x in g]
    er = []
    for (i, j) in E:
        a, b = g[i], g[j]
        R = a @ b @ a.conj().T - b @ b
        er.append(np.vdot(R, R).real / d)
        Gr[i] += (R @ a @ b.conj().T + R.conj().T @ a @ b) / d
        Gr[j] += (a.conj().T @ R @ a - R @ b.conj().T - b.conj().T @ R) / d
    Er = sum(er); e0 = info[0]
    G = [x / Er for x in Gr]
    G[0] = G[0] + np.eye(d) / (d * e0)
    S = []
    for idx, (x, Gx) in enumerate(zip(g, G)):
        X = x @ Gx.conj().T - (Gx.conj().T @ x if idx in iso else 0)
        S.append((X - X.conj().T) / 2)
    return J, S, info

def step_iso(g, D, t, iso):
    out = []
    for idx, (x, s) in enumerate(zip(g, D)):
        U = expm(t * s)
        out.append(U @ x @ U.conj().T if idx in iso else U @ x)
    return out

def cg_iso(g, E, iters, iso, tol=1e-13):
    J, S, info = objective_iso(g, E, iso)
    D = [s.copy() for s in S]
    t = 0.1
    for it in range(iters):
        n2 = sum(np.vdot(s, s).real for s in S)
        if n2 < tol:
            break
        slope = sum(np.vdot(dd, s).real for dd, s in zip(D, S))
        if slope <= 0:
            D, slope = [s.copy() for s in S], n2
        while True:
            gn = step_iso(g, D, t, iso)
            Jn, Sn, infon = objective_iso(gn, E, iso)
            if Jn <= J - 0.2 * t * 2 * slope or t < 1e-14:
                break
            t *= 0.5
        beta = max(0.0, sum(np.vdot(sn, sn - s).real for sn, s in zip(Sn, S)) / n2)
        D = [sn + beta * dd for sn, dd in zip(Sn, D)]
        g, J, S, info = gn, Jn, Sn, infon
        t = min(2 * t, 10.0)
    return g, J, info, it + 1
