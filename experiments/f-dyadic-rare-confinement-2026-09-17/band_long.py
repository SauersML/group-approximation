#!/usr/bin/env python3
"""Long-run band survival exponents, windowed, for F on the dyadics and a PSL2(Z) calibrator.

F: survival of the configuration chain T_i = h_i T_{i-1}, T_0 = D_C = {k/2^C}, killed when 1/2 leaves T_i.
   Its survival probability is exactly P(O_n subset D_C) (see cloning.py docstring).

PSL2(Z) on P^1(Q) (x_0 = infinity, mu uniform on {S, T, T^-1}, S x = -1/x, T x = x+1): same chain with
   T_0 = the Schreier ball of radius R around infinity.  This action is transitive with amenable
   stabilizer (the upper-triangular subgroup) and PSL2(Z) is nonamenable, so it is NOT extensively
   amenable (JMBMdlS Lemma 2.1 converse: EA + amenable stabilizers => amenable group); its band
   exponents must stay bounded away from 0.  Its Schreier graph, like F's dyadic graph, is a tree of
   horocycle lines, so it is the structural calibrator.

Reports the windowed rate -(log Z_t - log Z_{t-w})/w over the last windows, which converges faster than
the cumulative average.  Usage: python3 band_long.py [--N 500] [--n 3000] [--Cmax 7] [--Rmax 7]
Runtime with the defaults: about 10-20 minutes on one core; --quick about 1 minute.
"""
import argparse
import json
import math
import random
import time
from fractions import Fraction

import cloning as cl


def windowed(rng, N, n, start, step, w):
    pop = [start] * N
    logZ = 0.0
    marks = []
    for t in range(1, n + 1):
        new, ws = [], []
        for s in pop:
            s2, x = step(rng, s)
            new.append(s2)
            ws.append(x)
        tot = sum(ws)
        if tot == 0:
            return {"extinct_at": t}
        logZ += math.log(tot / N)
        pop = rng.choices(new, weights=ws, k=N)
        if t % w == 0:
            marks.append(logZ)
    rates = [-(marks[i] - (marks[i - 1] if i else 0.0)) / w for i in range(len(marks))]
    return {"cumulative": -logZ / n, "window": w, "window_rates": rates}


# PSL2(Z) on P^1(Q): points as reduced (p, q), q > 0 or (1, 0) for infinity
def norm(p, q):
    if q == 0:
        return (1, 0)
    g = math.gcd(p, q)
    p, q = p // g, q // g
    if q < 0:
        p, q = -p, -q
    return (p, q)


def S(pt):
    p, q = pt
    return norm(-q, p)


def Tp(pt):
    p, q = pt
    return (1, 0) if q == 0 else (p + q, q)


def Tm(pt):
    p, q = pt
    return (1, 0) if q == 0 else (p - q, q)


PGENS = [S, Tp, Tm]
INF = (1, 0)


def psl_band_step(rng, Tset):
    g = rng.choice(PGENS)
    T2 = frozenset(g(a) for a in Tset)
    return T2, (1.0 if INF in T2 else 0.0)


def psl_ball(R):
    ball = {INF}
    front = {INF}
    for _ in range(R):
        front = {g(a) for a in front for g in PGENS} - ball
        ball |= front
    return frozenset(ball)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=500)
    ap.add_argument("--n", type=int, default=3000)
    ap.add_argument("--Cmax", type=int, default=7)
    ap.add_argument("--Rmax", type=int, default=7)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--only", choices=["F", "PSL", "both"], default="both")
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    if a.quick:
        a.N, a.n, a.Cmax, a.Rmax = 200, 600, 5, 5
    rng = random.Random(a.seed)
    w = a.n // 6
    res = {"N": a.N, "n": a.n, "seed": a.seed}
    if a.only in ("F", "both"):
        for C in range(2, a.Cmax + 1):
            t0 = time.time()
            T0 = frozenset(k * (cl.U >> C) for k in range(1, 1 << C))
            r = windowed(rng, a.N, a.n, T0, cl.f_band_step, w)
            r["m"] = len(T0)
            res["F_band_C%d" % C] = r
            print("F C=%d m=%d %.0fs" % (C, len(T0), time.time() - t0),
                  {k: (round(v, 4) if isinstance(v, float) else [round(x, 4) for x in v] if isinstance(v, list) else v)
                   for k, v in r.items()}, flush=True)
    if a.only in ("PSL", "both"):
        for R in range(1, a.Rmax + 1):
            t0 = time.time()
            T0 = psl_ball(R)
            r = windowed(rng, a.N, a.n, T0, psl_band_step, w)
            r["m"] = len(T0)
            res["PSL_band_R%d" % R] = r
            print("PSL R=%d m=%d %.0fs" % (R, len(T0), time.time() - t0),
                  {k: (round(v, 4) if isinstance(v, float) else [round(x, 4) for x in v] if isinstance(v, list) else v)
                   for k, v in r.items()}, flush=True)
    res["inexact_halvings"] = cl.INEXACT[0]
    print("inexact halvings", cl.INEXACT[0])
    if a.out:
        with open(a.out, "w") as fh:
            json.dump(res, fh, indent=1)


if __name__ == "__main__":
    main()
