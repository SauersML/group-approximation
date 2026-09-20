#!/usr/bin/env python3
"""Check the bending lemma numerically.

For a periodic pattern (motif, v) at scale r = 1, bend N periods around a
circle of circumference N|v| and compare:
  (1) the r-graph of the finite bent set with the quotient graph G / N Z;
  (2) b_2 of the finite Rips complex with the Wang/Milnor prediction
      b_2(R(Y)/NZ) = dim coker(t^N - 1 | H_2(R(Y))) + dim ker(t^N - 1 | H_1(R(Y))),
      which is N * rank H_2 when H_2 is free and H_1 has no torsion at N-th
      roots of unity.  We print the computed b_2 next to N * (generic b_2).

Usage: python3 bend_check.py SEED TRIES   (draws 'hexa' patterns until one
has twisted b_2 > 0, then bends it for several N)
"""
import math
import random
import sys

from periodic_rips import P, periodic_graph_from_points, twisted_betti
from random_search import gen

BIG = (1.0e7, 0.0)  # a period so long that a finite set has no shifted edges


def bend(motif, v, N):
    vn = math.hypot(*v)
    ux, uy = v[0] / vn, v[1] / vn
    L = N * vn
    rho = L / (2 * math.pi)
    pts = []
    for j in range(N):
        for (x, y) in motif:
            X = (x * ux + y * uy) + j * vn
            Yc = -x * uy + y * ux
            th = X / rho
            pts.append(((rho + Yc) * math.cos(th), (rho + Yc) * math.sin(th)))
    return pts


def quotient_edges(k, adj, N):
    E = set()
    for i in range(k):
        for (i2, s) in adj[i]:
            for j in range(N):
                a = j * k + i
                b = ((j + s) % N) * k + i2
                if a != b:
                    E.add((min(a, b), max(a, b)))
    return E


def main():
    seed, tries = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    lr = rng.randrange(2, P - 1)
    for _ in range(tries):
        motif, v = gen("hexa", rng)
        k, adj, margin = periodic_graph_from_points(motif, v, 1.0)
        if margin < 1e-3:
            continue
        sizes, res = twisted_betti(k, adj, [1, lr])
        if res[lr][2] == 0:
            continue
        print("pattern k", k, "v", v, "margin", round(margin, 4),
              "twisted b(lam=1)", res[1], "b(generic)", res[lr], flush=True)
        vn = math.hypot(*v)
        for N in (8, 16, 32, 64):
            pts = bend(motif, v, N)
            n = len(pts)
            bent = {(a, b) for a in range(n) for b in range(a + 1, n)
                    if math.dist(pts[a], pts[b]) <= 1.0}
            quo = quotient_edges(k, adj, N)
            if N * vn <= 6:
                print("  N", N, "too small for the lemma (N|v| <= 6)")
            fk, fadj, _ = periodic_graph_from_points(pts, BIG, 1.0)
            _, fres = twisted_betti(fk, fadj, [1])
            print("  N", N, "graphs equal", bent == quo,
                  "finite b", fres[1], "N*generic b2", N * res[lr][2], flush=True)
        return
    print("no pattern with twisted b2 > 0 found")


if __name__ == "__main__":
    main()
