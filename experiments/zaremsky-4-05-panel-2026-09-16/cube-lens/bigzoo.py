"""Larger / higher-dimensional median graphs for the Helly and J searches.
Usage: python3 bigzoo.py seed iters qoff extra [names]
"""
import sys, random
import numpy as np
from mglib import MG, product, path, star, random_tree, RAAG
from graphs import raag_hull
import helly


def bigzoo(seed):
    rng = random.Random(seed)
    out = []
    P4 = [(0, 1), (1, 2), (2, 3)]
    a, b, c, d = [(i, 1) for i in range(4)]
    ai, bi, ci, di = [(i, -1) for i in range(4)]
    G, R, K = raag_hull(4, P4, [(), (a, c, a), (d, b, d), (c, d, ai)], "P4-hull2")
    out.append(MG(product(G.adj, path(2)), "P4hull2xP2"))
    out.append(MG(product(product(star(3), star(3)), star(3)), "K13^3"))
    out.append(MG(product(product(path(2), path(2)), product(path(2), path(2))), "Q4"))
    out.append(MG(product(product(star(3), path(2)), product(path(2), path(2))), "K13xQ3?"))
    # RAAG hulls with random words
    K1P4 = P4 + [(4, i) for i in range(4)]
    R = RAAG(5, K1P4)
    S = [()] + [R.random_word(rng, rng.randint(2, 4)) for _ in range(3)]
    out.append(raag_hull(5, K1P4, S, "K1*P4-rand")[0])
    TP = [(0, 1), (1, 2), (0, 2), (2, 3)]
    R = RAAG(4, TP)
    S = [()] + [R.random_word(rng, rng.randint(2, 4)) for _ in range(3)]
    out.append(raag_hull(4, TP, S, "tri+pend-rand")[0])
    # P4 RAAG random hull
    R = RAAG(4, P4)
    S = [()] + [R.random_word(rng, rng.randint(3, 5)) for _ in range(3)]
    out.append(raag_hull(4, P4, S, "P4-rand")[0])
    # K2*P4 (k=4) small hull
    K2P4 = P4 + [(4, i) for i in range(4)] + [(5, i) for i in range(5)]
    R = RAAG(6, K2P4)
    S = [()] + [R.random_word(rng, rng.randint(2, 3)) for _ in range(2)]
    out.append(raag_hull(6, K2P4, S, "K2*P4-rand")[0])
    return out


if __name__ == "__main__":
    seed = int(sys.argv[1]); iters = int(sys.argv[2]); qoff = int(sys.argv[3]); extra = int(sys.argv[4])
    names = sys.argv[5].split(",") if len(sys.argv) > 5 else None
    rng = random.Random(seed)
    for G in bigzoo(seed):
        if names and G.name not in names:
            continue
        print("graph", G.name, "n", G.n, "m", G.m, "k", G.k, "maxcubes", len(G.maxcubes), "median", G.median_ok,
              "ham", G.hamming_ok, flush=True)
        q = G.k + 1 + qoff
        ncent = q + 1 + extra
        if ncent > G.n or iters == 0:
            continue
        val, Z, lam, rho = helly.search(G, rng, iters, q, ncent)
        line = "  q=%d centres=%d bestF=%.3g" % (q, ncent, val)
        if val > 1e-7:
            full, subs = helly.verify_X(G, Z, list(rho), q)
            line += " | X-check: full=%.4g max_q_sub=%.4g Z=%s rho=%s" % (full, subs, Z, np.round(rho, 4).tolist())
        print(line, flush=True)
