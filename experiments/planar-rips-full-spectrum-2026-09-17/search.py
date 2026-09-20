#!/usr/bin/env python3
"""Full-spectrum H_2 torsion census for periodic planar Rips complexes (r = 1).

Usage: python3 search.py SEED N FAMILY [CAP]
Families: box hexa rows octa lattice (generators of random_search.py, copied
from the 2026-09-17 periodic-strip search) and new ones:
  circ    : 1-3 cyclic polygons per period with n = 3m points at the scale
            where one polygon alone is a wedge of m-1 two-spheres
  hexpair : two octahedral hexagons per period at centre distance 0.2..1.2
  dbox    : 12-24 uniform points in a box of height 0.8..1.6
For each pattern the exact torsion of H_2(R(Y); F_p) over F_p[t^{+-1}] is
computed (all eigenvalues).  Any torsion is printed as HIT.
"""
import math
import random
import sys
import time

from periodic_rips import periodic_graph_from_points, reduce_periodic
from random_search import gen as gen_old
from full_spectrum import h2_spectrum


def polygon(rng, cx, cy, m, jitter):
    n = 3 * m
    # n points on a circle, far graph: i ~ j far iff cyclic distance > m
    # chord of cyclic step m must be <= 1, step m+1 must be > 1
    lo = 1.0 / (2 * math.sin(math.pi * (m + 1) / n))
    hi = 1.0 / (2 * math.sin(math.pi * m / n))
    rad = rng.uniform(lo, hi) if lo < hi else lo
    th0 = rng.uniform(0, 2 * math.pi)
    return [(cx + rad * math.cos(th0 + 2 * math.pi * i / n) + rng.gauss(0, jitter),
             cy + rad * math.sin(th0 + 2 * math.pi * i / n) + rng.gauss(0, jitter))
            for i in range(n)]


def gen(fam, rng):
    if fam == "circ":
        p = rng.uniform(0.3, 2.5)
        motif = []
        for q in range(rng.randint(1, 3)):
            m = rng.choice([2, 2, 3])
            motif += polygon(rng, rng.uniform(0, p), rng.uniform(-0.4, 0.4), m,
                             rng.choice([0.0, 0.01, 0.03]))
        for _ in range(rng.randint(0, 2)):
            motif.append((rng.uniform(0, p), rng.uniform(-0.8, 0.8)))
        return motif, (p, 0.0)
    if fam == "hexpair":
        d = rng.uniform(0.2, 1.2)
        ang = rng.uniform(0, math.pi)
        motif = polygon(rng, 0, 0, 2, 0.02) + polygon(
            rng, d * math.cos(ang), d * math.sin(ang), 2, 0.02)
        p = rng.uniform(0.3, 2.6)
        th = rng.uniform(-0.3, 0.3)
        return motif, (p * math.cos(th), p * math.sin(th))
    if fam == "dbox":
        k = rng.randint(12, 24)
        p = rng.uniform(0.3, 2.0)
        w = rng.uniform(0.8, 1.6)
        return [(rng.uniform(0, p), rng.uniform(0, w)) for _ in range(k)], (p, 0.0)
    return gen_old(fam, rng)


def main():
    seed, N, fam = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 4000
    rng = random.Random(seed)
    st = {"done": 0, "skipped": 0, "h2free": 0, "hits": 0, "maxresid": 0}
    t0 = time.time()
    for n in range(N):
        if n and n % 100 == 0:
            print("PROGRESS", fam, seed, n, st, round(time.time() - t0, 1), flush=True)
        motif, v = gen(fam, rng)
        if len(set((round(x, 9), round(y, 9)) for x, y in motif)) < len(motif):
            st["skipped"] += 1
            continue
        k, adj, margin = periodic_graph_from_points(motif, v, 1.0)
        if margin < 1e-6:
            st["skipped"] += 1
            continue
        try:
            k2, adj2, kept = reduce_periodic(k, adj)
            res = h2_spectrum(k2, adj2, cap=cap, seed=seed * 100003 + n)
        except MemoryError:
            # run under prlimit --as; oversized clique enumerations are skipped
            st["skipped"] += 1
            continue
        if res["skipped"]:
            st["skipped"] += 1
            continue
        st["done"] += 1
        st["maxresid"] = max(st["maxresid"], res["residual"][0])
        if res["h2_free_rank"] > 0:
            st["h2free"] += 1
        if res["torsion"]:
            st["hits"] += 1
            print("HIT", fam, seed, n, res, "motif",
                  [(round(x, 9), round(y, 9)) for x, y in motif], "v", v, flush=True)
    print("SUMMARY", fam, seed, st, round(time.time() - t0, 1), flush=True)


if __name__ == "__main__":
    main()
