#!/usr/bin/env python3
"""Random search for periodic strip patterns with a twisted b_2 jump.

Usage: python3 random_search.py SEED N FAMILY
FAMILY: box (uniform motif in a p x w box), hexa (octahedral hexagons with
jitter, several per period), rows (points on a few horizontal rows).
Prints a line for each pattern whose twisted Betti numbers differ between
lam = 1, lam = -1 and a random lam (a candidate certificate), and a summary.
"""
import math
import random
import sys
import time

from periodic_rips import (P, periodic_graph_from_points, reduce_periodic,
                           twisted_betti, cliques)

MAXCELLS = 6000


def gen(fam, rng):
    if fam == "box":
        k = rng.randint(5, 16)
        p = rng.uniform(0.25, 2.5)
        w = rng.uniform(0.6, 1.8)
        motif = [(rng.uniform(0, p), rng.uniform(0, w)) for _ in range(k)]
        return motif, (p, 0.0)
    if fam == "hexa":
        # h hexagons per period, radius ~ 0.5 (r = 1 sits between sqrt3/2 and 1)
        h = rng.randint(1, 3)
        p = rng.uniform(0.4, 2.2)
        motif = []
        for q in range(h):
            cx = rng.uniform(0, p)
            cy = rng.uniform(-0.3, 0.3)
            rad = rng.uniform(0.505, 0.57)
            th0 = rng.uniform(0, math.pi / 3)
            for i in range(6):
                if rng.random() < 0.15:
                    continue
                th = th0 + i * math.pi / 3 + rng.gauss(0, 0.06)
                rr = rad * (1 + rng.gauss(0, 0.03))
                motif.append((cx + rr * math.cos(th), cy + rr * math.sin(th)))
        for _ in range(rng.randint(0, 3)):
            motif.append((rng.uniform(0, p), rng.uniform(-0.7, 0.7)))
        return motif, (p, 0.0)
    if fam == "rows":
        nr = rng.randint(2, 5)
        p = rng.uniform(0.3, 2.0)
        motif = []
        for q in range(nr):
            y = rng.uniform(-0.8, 0.8)
            for _ in range(rng.randint(1, 4)):
                motif.append((rng.uniform(0, p), y + rng.gauss(0, 0.02)))
        return motif, (p, 0.0)
    if fam == "octa":
        # one octahedral 6-set (far graph a perfect matching at r = 1),
        # translated by a short vector v: the rigid sliding track.
        while True:
            rad = rng.uniform(0.5, 0.6)
            th0 = rng.uniform(0, math.pi)
            sq = rng.uniform(0.6, 1.0)  # squash factor
            pts = []
            for i in range(6):
                th = th0 + i * math.pi / 3 + rng.gauss(0, 0.12)
                rr = rad * (1 + rng.gauss(0, 0.08))
                pts.append((rr * math.cos(th), sq * rr * math.sin(th) / max(sq, 0.85)))
            far = [(i, j) for i in range(6) for j in range(i + 1, 6)
                   if math.dist(pts[i], pts[j]) > 1.0]
            deg = [0] * 6
            for i, j in far:
                deg[i] += 1
                deg[j] += 1
            if len(far) == 3 and deg == [1] * 6:
                break
        L = rng.uniform(0.02, 0.6)
        th = rng.uniform(0, math.pi)
        extra = [(rng.uniform(-0.7, 0.7), rng.uniform(-0.7, 0.7))
                 for _ in range(rng.choice([0, 0, 1, 2]))]
        return pts + extra, (L * math.cos(th), L * math.sin(th))
    if fam == "lattice":
        # W rows of a square or triangular lattice, period of c columns,
        # scale 1 placed near a critical lattice distance, small periodic jitter.
        tri = rng.random() < 0.5
        W = rng.randint(2, 5)
        c = rng.randint(1, 3)
        dists = sorted({math.hypot(a + (0.5 * b if tri else 0), b * (math.sqrt(3) / 2 if tri else 1))
                        for a in range(-4, 5) for b in range(0, 4)} - {0.0})
        dcrit = rng.choice([d for d in dists if 1.0 <= d <= 3.0])
        a = (1.0 / dcrit) * (1 + rng.uniform(-0.04, 0.04))
        jit = rng.choice([0.0, 0.01, 0.03])
        motif = []
        for row in range(W):
            for col in range(c):
                x = (col + (0.5 * row if tri else 0)) * a
                y = row * a * (math.sqrt(3) / 2 if tri else 1)
                motif.append((x + rng.gauss(0, jit * a), y + rng.gauss(0, jit * a)))
        return motif, (c * a, 0.0)
    raise SystemExit("unknown family")


def main():
    seed, N, fam = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    rng = random.Random(seed)
    lr = rng.randrange(2, P - 1)
    stats = {"done": 0, "skipped": 0, "h2": 0, "hits": 0}
    t0 = time.time()
    for n in range(N):
        motif, v = gen(fam, rng)
        k, adj, margin = periodic_graph_from_points(motif, v, 1.0)
        if margin < 1e-6:
            stats["skipped"] += 1
            continue
        k2, adj2, kept = reduce_periodic(k, adj)
        cl = cliques(k2, adj2, 4)
        if sum(len(c) for c in cl.values()) > MAXCELLS:
            stats["skipped"] += 1
            continue
        sizes, res = twisted_betti(k2, adj2, [1, P - 1, lr])
        stats["done"] += 1
        bs = [tuple(res[l]) for l in (1, P - 1, lr)]
        if res[lr][2] > 0 or res[1][2] > 0:
            stats["h2"] += 1
        if bs[0][2] != bs[2][2] or bs[1][2] != bs[2][2]:
            stats["hits"] += 1
            print("HIT", fam, seed, n, "betti", bs, "sizes", sizes,
                  "motif", [(round(x, 6), round(y, 6)) for x, y in motif], "v", v,
                  flush=True)
    print("SUMMARY", fam, seed, stats, round(time.time() - t0, 1), flush=True)


if __name__ == "__main__":
    main()
