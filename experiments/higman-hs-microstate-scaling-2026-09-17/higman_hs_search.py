#!/usr/bin/env python3
"""Large-dimension normalized-HS microstate search for Higman-type BS cycles.

Relators, for i on a graph (cycle Z/k or path 0..k-1):
    r_i = g_i g_{i+1} g_i^* - g_{i+1}^2 .
Defect  delta^2 = sum_i ||r_i||_2^2   with ||X||_2^2 = tr(X^* X)/d.

Mark control: every g_i is kept isospectral to a fixed diagonal Lambda
(default: all d-th roots of unity, d odd), so ||g_i - 1||_2^2 = 2 - 2 Re tr(Lambda)/d
is frozen (= 2 for the full root set).  We minimize over the gauges only:
g_i <- exp(eta S_i) g_i exp(-eta S_i), S_i skew-Hermitian.

Calibrations:
  * cycle k=3 : Higman's 3-generator group is trivial, so a dimension-free
    linear bound  ||g_0-1||_2 <= C delta  holds; the search must show a floor.
  * path  k=4 : an iterated amalgam of BS(1,2) over Z, sofic; microstates exist.
Target:
  * cycle k=4 : Higman's group H4 (open).

Usage: higman_hs_search.py --topo cycle --k 4 --d 31 --restarts 4 --iters 3000 --seed 0
"""
import argparse, json, sys, time
import numpy as np
from scipy.linalg import expm

def edges(topo, k):
    if topo == "cycle":
        return [(i, (i + 1) % k) for i in range(k)]
    return [(i, i + 1) for i in range(k - 1)]

def energy_grad(g, E):
    d = g[0].shape[0]
    val = 0.0
    G = [np.zeros_like(x) for x in g]
    res = []
    for (i, j) in E:
        a, b = g[i], g[j]
        R = a @ b @ a.conj().T - b @ b
        n2 = np.vdot(R, R).real / d
        res.append(n2)
        val += n2
        # d||R||^2 = 2 Re <G, dg>, Euclidean gradient (unnormalized, then /d)
        G[i] += (R @ a @ b.conj().T + R.conj().T @ a @ b) / d
        G[j] += (a.conj().T @ R @ a - R @ b.conj().T - b.conj().T @ R) / d
    # isospectral direction: X = g G^* - G^* g, descent generator = skew part
    S = []
    for x, Gx in zip(g, G):
        X = x @ Gx.conj().T - Gx.conj().T @ x
        S.append((X - X.conj().T) / 2)
    return val, S, res

def conj_step(g, S, eta, frozen):
    out = []
    for idx, (x, s) in enumerate(zip(g, S)):
        if idx in frozen:
            out.append(x)
            continue
        U = expm(eta * s)
        out.append(U @ x @ U.conj().T)
    return out

def haar(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    ph = np.diag(r) / np.abs(np.diag(r))
    return q * ph

def spectrum(d, kind):
    if kind == "roots":
        return np.exp(2j * np.pi * np.arange(d) / d)
    raise ValueError(kind)

def optimize(topo, k, d, iters, rng, kind="roots", tol=1e-12, log_every=0):
    E = edges(topo, k)
    lam = spectrum(d, kind)
    g = []
    for i in range(k):
        W = haar(d, rng)
        g.append((W * lam) @ W.conj().T)
    frozen = {0}
    val, S, res = energy_grad(g, E)
    eta = 0.5
    prevS, prevg = None, None
    hist = []
    for it in range(iters):
        nrm2 = sum(np.vdot(s, s).real for s in S)
        if nrm2 < tol:
            break
        # Armijo backtracking
        while True:
            gn = conj_step(g, S, eta, frozen)
            vn, Sn, resn = energy_grad(gn, E)
            if vn <= val - 0.3 * eta * 2 * nrm2 or eta < 1e-8:
                break
            eta *= 0.5
        g, val, S, res = gn, vn, Sn, resn
        eta = min(eta * 1.6, 50.0)
        if log_every and it % log_every == 0:
            hist.append((it, val))
    mark = [2 - 2 * np.trace(x).real / d for x in g]
    return dict(topo=topo, k=k, d=d, delta2=val, delta=float(np.sqrt(val)),
                per_relator=[float(r) for r in res], mark2=[float(m) for m in mark],
                iters=it + 1, hist=hist), g

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--topo", default="cycle")
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--d", type=int, default=15)
    ap.add_argument("--restarts", type=int, default=2)
    ap.add_argument("--iters", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default="")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    best = None
    for r in range(a.restarts):
        t = time.time()
        res, g = optimize(a.topo, a.k, a.d, a.iters, rng)
        res["restart"] = r
        res["secs"] = time.time() - t
        print(json.dumps({kk: res[kk] for kk in ("topo", "k", "d", "restart", "delta", "iters", "secs")}), flush=True)
        if best is None or res["delta2"] < best[0]["delta2"]:
            best = (res, g)
    if a.out:
        np.savez_compressed(a.out, *best[1])
    print("BEST", json.dumps({kk: best[0][kk] for kk in ("topo", "k", "d", "delta", "per_relator", "mark2")}))

if __name__ == "__main__":
    main()

def flow(g, E, iters, frozen=(0,), tol=1e-14, log_every=0):
    """Isospectral Armijo gradient flow from a given start; returns (g, val, res, hist)."""
    frozen = set(frozen)
    val, S, res = energy_grad(g, E)
    S = [np.zeros_like(s) if i in frozen else s for i, s in enumerate(S)]
    eta, hist = 0.5, []
    for it in range(iters):
        nrm2 = sum(np.vdot(s, s).real for s in S)
        if nrm2 < tol:
            break
        while True:
            gn = conj_step(g, S, eta, frozen)
            vn, Sn, resn = energy_grad(gn, E)
            if vn <= val - 0.3 * eta * 2 * nrm2 or eta < 1e-10:
                break
            eta *= 0.5
        g, val, res = gn, vn, resn
        S = [np.zeros_like(s) if i in frozen else s for i, s in enumerate(Sn)]
        eta = min(eta * 1.6, 100.0)
        if log_every and it % log_every == 0:
            hist.append((it, float(val), [float(r) for r in res]))
    return g, val, res, hist

def cg_flow(g, E, iters, frozen=(0,), tol=1e-14, log_every=0):
    """Isospectral nonlinear CG (PR+, identity transport, Armijo on descent)."""
    frozen = set(frozen)
    def mask(S):
        return [np.zeros_like(s) if i in frozen else s for i, s in enumerate(S)]
    val, S, res = energy_grad(g, E)
    S = mask(S)  # S = -gradient generator (descent)
    Dir = [s.copy() for s in S]
    eta, hist = 0.5, []
    for it in range(iters):
        nrm2 = sum(np.vdot(s, s).real for s in S)
        if nrm2 < tol:
            break
        slope = sum(np.trace(dd.conj().T @ s).real for dd, s in zip(Dir, S))
        if slope <= 0:
            Dir = [s.copy() for s in S]
            slope = nrm2
        while True:
            gn = conj_step(g, Dir, eta, frozen)
            vn, Sn, resn = energy_grad(gn, E)
            if vn <= val - 0.2 * eta * 2 * slope or eta < 1e-12:
                break
            eta *= 0.5
        Sn = mask(Sn)
        beta = sum(np.vdot(sn, sn - s).real for sn, s in zip(Sn, S)) / nrm2
        beta = max(0.0, beta)
        Dir = [sn + beta * dd for sn, dd in zip(Sn, Dir)]
        g, val, res, S = gn, vn, resn, Sn
        eta = min(eta * 2.0, 100.0)
        if log_every and it % log_every == 0:
            hist.append((it, float(val)))
    return g, val, res, hist
