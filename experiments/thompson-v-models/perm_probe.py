"""Normalized-Hamming (permutation) almost-actions of Thompson's V: a numerical probe.

Run on MSI only.  Presentation: Bleak--Quick u, v with seven relators
(presentation_bq2.json).  n is a multiple of 6.  u is conjugate to a fixed
permutation all of whose cycles have length 6, and v to one all of whose cycles
have length 3, so u^6 = v^3 = 1 hold exactly and every power u^k (k=1..5) and v
moves every point: the marked a = u^3 is fixed-point-free.  Simulated annealing
over the two conjugators (moves: transpose two entries) minimizes the mean over
the five remaining relators of the proportion of points a relator moves.

A sofic approximation of V would give models with this cost tending to 0 as n
grows.  The probe reports the best cost found per n, so the trend in n is the
signal, and it is heuristic: annealing can miss good models.

Usage: python3 perm_probe.py --ns 36 72 144 288 --seeds 3 --steps 200000 --out FILE.json
"""
import argparse
import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import texwords

HERE = os.path.dirname(os.path.abspath(__file__))
P = json.load(open(os.path.join(HERE, "presentation_bq2.json")))
RELATORS = [texwords.parse(r) for r in P["relators_tex"][2:]]


def cyc_perm(n, k):
    """Permutation of range(n) made of n/k consecutive k-cycles."""
    p = np.arange(n)
    for start in range(0, n, k):
        block = np.arange(start, start + k)
        p[block] = np.roll(block, -1)
    return p


def conj(tau, base):
    """tau^-1 base tau as a map x -> tau[base[tau^-1[x]]] (a conjugate with the same cycle type)."""
    inv = np.empty_like(tau)
    inv[tau] = np.arange(len(tau))
    return tau[base[inv]]


def inverse(p):
    q = np.empty_like(p)
    q[p] = np.arange(len(p))
    return q


def cost(g, ginv, n):
    tot = 0.0
    per = []
    x0 = np.arange(n)
    for word in RELATORS:
        x = x0
        for letter, e in word:
            x = (g[letter] if e > 0 else ginv[letter])[x]
        moved = float(np.count_nonzero(x != x0)) / n
        per.append(moved)
        tot += moved
    return tot / len(RELATORS), per


def anneal(n, seed, steps, T0, T1):
    rng = np.random.default_rng(seed)
    base = {"u": cyc_perm(n, 6), "v": cyc_perm(n, 3)}
    tau = {"u": rng.permutation(n), "v": rng.permutation(n)}

    def build(tau):
        g = {x: conj(tau[x], base[x]) for x in "uv"}
        return g, {x: inverse(g[x]) for x in "uv"}

    g, ginv = build(tau)
    c, per = cost(g, ginv, n)
    c0 = c
    best = (c, per)
    t0 = time.time()
    for s in range(steps):
        T = T0 * (T1 / T0) ** (s / max(1, steps - 1))
        x = "u" if rng.random() < 0.5 else "v"
        i, j = rng.integers(0, n, size=2)
        if i == j:
            continue
        tau[x][i], tau[x][j] = tau[x][j], tau[x][i]
        g2, ginv2 = build(tau)
        c2, per2 = cost(g2, ginv2, n)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) * n / T):
            g, ginv, c, per = g2, ginv2, c2, per2
            if c < best[0]:
                best = (c, per)
        else:
            tau[x][i], tau[x][j] = tau[x][j], tau[x][i]
    return {"n": n, "seed": seed, "initial_cost": c0, "best_cost": best[0],
            "best_per_relator": best[1], "seconds": time.time() - t0}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", type=int, nargs="+", default=[36, 72, 144])
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--steps", type=int, default=100000)
    ap.add_argument("--T0", type=float, default=2.0)
    ap.add_argument("--T1", type=float, default=0.02)
    ap.add_argument("--out", default="perm_probe_results.json")
    a = ap.parse_args()
    results = []
    for n in a.ns:
        assert n % 6 == 0
        for s in range(a.seeds):
            r = anneal(n, s, a.steps, a.T0, a.T1)
            results.append(r)
            print(json.dumps(r), flush=True)
            json.dump(results, open(a.out, "w"), indent=1)
