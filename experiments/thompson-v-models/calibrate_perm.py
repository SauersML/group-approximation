"""Calibrate the permutation (Hamming) probe of Thompson's V (perm_probe.py) on a planted control.

Run on MSI only.  Same parametrization and annealer as perm_probe.py: u conjugate to a fixed
product of disjoint 6-cycles and v to one of disjoint 3-cycles on n points, so u^6 = v^3 = 1
exactly and u^3 is fixed-point-free; simulated annealing over the two conjugators minimizes the
mean fraction of points moved by the five remaining relators.  Relator sets (calibrate_hs.py):

  V        the Bleak--Quick words;
  planted  the same words raised to their orders in S_5.  The left regular action of S_5 on
           itself (n = 120) sends x (cycle type (2)(3), order 6) to 20 disjoint 6-cycles and a
           3-cycle y to 40 disjoint 3-cycles, so an EXACT solution exists at n = 120k;
  null     random words of the same lengths.

Convention.  perm_probe's cost applies the letters of a word left to right to points, which
composes permutations in the opposite order to the matrix products of calibrate_hs.py.  Every
relator is therefore reversed before annealing, so the planted words vanish exactly as they do
in the matrix convention.  For V this probes the presentation with u, v replaced by their
inverses, which presents the same group.

Usage: python3 calibrate_perm.py --sets planted V null --ns 120 240 --seeds 2 --steps 100000 --out FILE.json
"""
import argparse
import itertools
import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import calibrate_hs as C
import perm_probe as PP


def cost(g, ginv, n, rels):
    tot, per = 0.0, []
    x0 = np.arange(n)
    for word in rels:
        x = x0
        for letter, e in word:
            x = (g[letter] if e > 0 else ginv[letter])[x]
        moved = float(np.count_nonzero(x != x0)) / n
        per.append(moved)
        tot += moved
    return tot / len(rels), per


def anneal(n, seed, steps, T0, T1, rels):
    rng = np.random.default_rng(seed)
    base = {"u": PP.cyc_perm(n, 6), "v": PP.cyc_perm(n, 3)}
    tau = {"u": rng.permutation(n), "v": rng.permutation(n)}

    def build(tau):
        g = {x: PP.conj(tau[x], base[x]) for x in "uv"}
        return g, {x: PP.inverse(g[x]) for x in "uv"}

    g, ginv = build(tau)
    c, per = cost(g, ginv, n, rels)
    best = (c, per)
    t0 = time.time()
    for s in range(steps):
        if best[0] == 0.0:
            break
        T = T0 * (T1 / T0) ** (s / max(1, steps - 1))
        x = "u" if rng.random() < 0.5 else "v"
        i, j = rng.integers(0, n, size=2)
        if i == j:
            continue
        tau[x][i], tau[x][j] = tau[x][j], tau[x][i]
        g2, ginv2 = build(tau)
        c2, per2 = cost(g2, ginv2, n, rels)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) * n / T):
            g, ginv, c, per = g2, ginv2, c2, per2
            if c < best[0]:
                best = (c, per)
        else:
            tau[x][i], tau[x][j] = tau[x][j], tau[x][i]
    return {"n": n, "seed": seed, "best_cost": best[0], "best_per_relator": best[1],
            "steps_done": s + 1, "seconds": time.time() - t0}


def regular_action_check(rels):
    """Exact solution at n = 120: left regular action of S_5 on itself."""
    x, y = None, None
    import basin_hs as B
    x, y = B.planted_generators(0)
    elems = []
    seen = {tuple(range(5))}
    frontier = [tuple(range(5))]
    while frontier:
        nxt = []
        for h in frontier:
            for s in (x, y):
                k = tuple(s[h[i]] for i in range(5))
                if k not in seen:
                    seen.add(k)
                    nxt.append(k)
        frontier = nxt
    elems = sorted(seen)
    index = {e: i for i, e in enumerate(elems)}

    def left_mult(p):
        return np.array([index[tuple(p[e[i]] for i in range(5))] for e in elems])

    g = {"u": left_mult(x), "v": left_mult(y)}
    ginv = {k: PP.inverse(v) for k, v in g.items()}
    return cost(g, ginv, 120, rels)[0]


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--sets", nargs="+", default=["planted", "V", "null"])
    ap.add_argument("--ns", type=int, nargs="+", default=[120, 240])
    ap.add_argument("--seeds", type=int, default=2)
    ap.add_argument("--steps", type=int, default=100000)
    ap.add_argument("--T0", type=float, default=2.0)
    ap.add_argument("--T1", type=float, default=0.02)
    ap.add_argument("--out", default="calibrate_perm_results.json")
    a = ap.parse_args()
    results = []
    rels0, _ = C.planted_s5_relators(0)
    rels0 = [list(reversed(w)) for w in rels0]
    print(json.dumps({"planted_seed0_regular_action_cost_n120": regular_action_check(rels0)}), flush=True)
    for name, n, s in itertools.product(a.sets, a.ns, range(a.seeds)):
        if name == "V":
            rels = C.V_RELATORS
        elif name == "planted":
            rels, _ = C.planted_s5_relators(s)
        elif name == "null":
            rels = C.null_relators(s)
        else:
            raise ValueError(name)
        rels = [list(reversed(w)) for w in rels]
        r = anneal(n, s, a.steps, a.T0, a.T1, rels)
        r["set"] = name
        results.append(r)
        print(json.dumps({k: r[k] for k in ("set", "n", "seed", "best_cost", "steps_done", "seconds")}), flush=True)
        json.dump(results, open(a.out, "w"), indent=1)
