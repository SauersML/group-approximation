#!/usr/bin/env python3
"""Windowed cloning estimate of Lambda = lim -(1/n) log E 2^{-|O_n|} for F on the dyadics and for the
PSL2(Z) on P^1(Q) calibrator (non-EA, Lambda_PSL >= -log((1+rho_PSL)/2) > 0).

Same chain as cloning.py: S_k = {x_0} u h_k S_{k-1}, weight 1/2 whenever x_0 was not already in h_k S_{k-1}.
Usage: python3 lambda_long.py [--N 1000] [--n 4000] [--which F|PSL|both] [--out FILE]
Runtime with defaults: roughly 10-25 minutes per model on one core.
"""
import argparse
import json
import random
import time

import band_long as bl
import cloning as cl


def psl_orbit_step(rng, S):
    g = rng.choice(bl.PGENS)
    S2 = frozenset(g(a) for a in S)
    if bl.INF in S2:
        return S2, 1.0
    return S2 | {bl.INF}, 0.5


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=1000)
    ap.add_argument("--n", type=int, default=4000)
    ap.add_argument("--seed", type=int, default=11)
    ap.add_argument("--which", choices=["F", "PSL", "both"], default="both")
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    w = a.n // 8
    res = {"N": a.N, "n": a.n, "seed": a.seed}
    models = []
    if a.which in ("F", "both"):
        models.append(("F_dyadic", frozenset([cl.X0]), cl.f_orbit_step))
    if a.which in ("PSL", "both"):
        models.append(("PSL_P1Q", frozenset([bl.INF]), psl_orbit_step))
    for name, start, step in models:
        t0 = time.time()
        r = bl.windowed(rng, a.N, a.n, start, step, w)
        res[name] = r
        print(name, "%.0fs" % (time.time() - t0), "cumulative %.4f" % r["cumulative"],
              "windows", [round(x, 4) for x in r["window_rates"]], flush=True)
    res["inexact_halvings"] = cl.INEXACT[0]
    if a.out:
        with open(a.out, "w") as fh:
            json.dump(res, fh, indent=1)


if __name__ == "__main__":
    main()
