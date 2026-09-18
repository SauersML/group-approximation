#!/usr/bin/env python3
"""Checks for fpbs-hp-thinning-two-point-exit.

1. Exact disagreement recursion of the Hutchcroft--Pete scheme
   D_1 = 2p(1-p),  D_{i+1} = q D_i (2u - q D_i / 2),  u = sqrt(1-p), q = 1/(1+u),
   checked by Monte Carlo on a periodic L x L torus (any vertex-transitive graph works,
   the identity only uses: occupied neighbours lie in one cluster, and the two thinned
   copies are independent).
2. The exit stage bound i_0(p, rho) = min{i : D_i < 2(1-rho) p} and the one-step
   ratio floor r(p) = q(2u - q p(1-p)).
3. Free-group calibration: for Bernoulli(p) site percolation on the 2r-regular tree,
   sum_g m^{*n}(g) tau(g) = p E[p^{|X_n|}]. Its exponential rate is compared with
   rho = sqrt(2r-1)/r; the necessary condition of (T2) fails exactly when the rate
   exceeds rho, predicted for p > 1/sqrt(2r-1).

Run: nice -n 10 timeout 1200 python3 recursion_check.py
"""
import math
import sys

import numpy as np


def recursion(p, n):
    u = math.sqrt(1 - p)
    q = 1 / (1 + u)
    D = [2 * p * (1 - p)]
    for _ in range(n - 1):
        d = D[-1]
        D.append(q * d * (2 * u - q * d / 2))
    return D


def ratio_floor(p):
    u = math.sqrt(1 - p)
    q = 1 / (1 + u)
    return q * (2 * u - q * p * (1 - p))


def exit_bound(p, rho, cap=10 ** 7):
    u = math.sqrt(1 - p)
    q = 1 / (1 + u)
    d = 2 * p * (1 - p)
    i = 1
    while d >= 2 * (1 - rho) * p:
        d = q * d * (2 * u - q * d / 2)
        i += 1
        if i > cap:
            return None
    return i


# ---------- Monte Carlo on the torus ----------

def find(parent, x):
    root = x
    while parent[root] != root:
        root = parent[root]
    while parent[x] != root:
        parent[x], x = root, parent[x]
    return root


def cluster_labels(occ):
    L = occ.shape[0]
    n = L * L
    parent = list(range(n))
    flat = occ.ravel()
    for idx in np.flatnonzero(flat):
        i, j = divmod(int(idx), L)
        for (a, b) in (((i + 1) % L, j), (i, (j + 1) % L)):
            jdx = a * L + b
            if flat[jdx]:
                ra, rb = find(parent, int(idx)), find(parent, jdx)
                if ra != rb:
                    parent[ra] = rb
    return np.array([find(parent, k) for k in range(n)]).reshape(L, L)


def sample_stage(i, p, q, L, rng):
    if i == 1:
        return rng.random((L, L)) < p
    out = np.zeros((L, L), dtype=bool)
    for _ in range(2):
        w = sample_stage(i - 1, p, q, L, rng)
        lab = cluster_labels(w)
        keep = {}
        thinned = np.zeros((L, L), dtype=bool)
        for (a, b) in zip(*np.nonzero(w)):
            r = lab[a, b]
            if r not in keep:
                keep[r] = rng.random() < q
            thinned[a, b] = keep[r]
        out |= thinned
    return out


def disagreement(w):
    return 0.5 * (np.mean(w != np.roll(w, 1, 0)) + np.mean(w != np.roll(w, 1, 1)))


def monte_carlo(p=0.3, L=32, stages=4, trials=300, seed=20260917):
    rng = np.random.default_rng(seed)
    u = math.sqrt(1 - p)
    q = 1 / (1 + u)
    pred = recursion(p, stages)
    print(f"[MC] torus {L}x{L}, p={p}, trials={trials}")
    ok = True
    for i in range(1, stages + 1):
        ds, dens = [], []
        for _ in range(trials):
            w = sample_stage(i, p, q, L, rng)
            ds.append(disagreement(w))
            dens.append(w.mean())
        m, se = float(np.mean(ds)), float(np.std(ds) / math.sqrt(trials))
        z = (m - pred[i - 1]) / se if se > 0 else 0.0
        ok &= abs(z) < 4
        print(f"  stage {i}: density {np.mean(dens):.4f} (p={p}); D MC {m:.5f} +- {se:.5f}; "
              f"predicted {pred[i - 1]:.5f}; z={z:+.2f}")
    return ok


# ---------- free group calibration ----------

def tree_rate(p, r, n, lag=500):
    """Exponential rate of E p^{|X_n|} for simple random walk on the 2r-regular tree.

    Exact backward iteration f <- P f of the distance chain on {0, ..., n+1}, started from
    f(k) = p^k; then E p^{|X_n|} = (P^n f)(0). Values at distance > n from 0 never reach
    f(0) within n steps, so the cut at n+1 is exact. f is renormalized by its maximum each
    step (all entries are nonnegative) and the logarithm of the scale is tracked. The rate
    is the log-slope over the last `lag` steps, removing the polynomial prefactor to first
    order.
    """
    d = 2 * r
    K = n + 1
    f = p ** np.arange(K + 1, dtype=float)
    logscale = 0.0
    logs = {}
    for step in range(1, n + 1):
        g = np.empty_like(f)
        g[0] = f[1]
        g[1:-1] = (d - 1) / d * f[2:] + f[:-2] / d
        g[-1] = f[-1]
        m = g.max()
        f = g / m
        logscale += math.log(m)
        if step in (n - lag, n):
            logs[step] = math.log(f[0]) + logscale
    return math.exp((logs[n] - logs[n - lag]) / lag)


def main():
    ok = monte_carlo()

    print("\n[recursion] D_i/p, ratio floor r(p), and exit bound i_0(p, rho)")
    for p in (0.2, 0.1, 0.05, 0.01):
        D = recursion(p, 6)
        print(f"  p={p}: D_1..D_6 / p = " + ", ".join(f"{x / p:.4f}" for x in D)
              + f"; r(p)={ratio_floor(p):.5f}; 1-p/2={1 - p / 2:.5f}")
        for rho in (0.5, 0.8, 0.95):
            print(f"      rho={rho}: i_0={exit_bound(p, rho)}  "
                  f"(4/p) log(1/(1-rho)) = {4 / p * math.log(1 / (1 - rho)):.1f}")

    print("\n[free group] rate of E p^{|X_n|} vs rho, n=4000 (log-slope over last 500 steps)")
    for r in (2, 3):
        rho = math.sqrt(2 * r - 1) / r
        pc = 1 / (2 * r - 1)
        thr = 1 / math.sqrt(2 * r - 1)
        print(f"  F_{r}: rho={rho:.5f}, p_c={pc:.4f}, 1/sqrt(2r-1)={thr:.4f}, C(b)-1={r - 1}")
        for p in (pc, 0.5 * (pc + thr), 0.5 * (thr + 1), 0.9):
            rate = tree_rate(p, r, 4000)
            gamma = (1 / p + (2 * r - 1) * p) / (2 * r)
            predicted = rho if p <= thr else gamma
            exceeds = rate > rho * (1 + 2e-3)
            ok &= abs(rate - predicted) < 3e-3 and exceeds == (p > thr * (1 + 1e-9))
            print(f"    p={p:.4f}: rate {rate:.5f}; predicted rate {predicted:.5f} "
                  f"(gamma(p)={gamma:.5f}); necessary condition violated: {exceeds}")
    print("\nALL_OK" if ok else "\nFAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
