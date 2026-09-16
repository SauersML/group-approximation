"""Test graph zoo for the cube-lens panel checks."""
import random
from mglib import MG, product, path, star, random_tree, RAAG, buneman


def raag_hull(nv, edges, S_words, name):
    R = RAAG(nv, edges)
    K = R.hull(S_words)
    return MG(R.graph(K), name=name), R, K


def zoo(seed=0, big=False):
    rng = random.Random(seed)
    out = []
    out.append(MG(path(4), "P4"))
    out.append(MG(star(3), "K13"))
    out.append(MG(product(path(3), path(3)), "grid3x3"))
    out.append(MG(product(path(4), path(3)), "grid4x3"))
    out.append(MG(product(product(path(2), path(2)), path(2)), "Q3"))
    out.append(MG(product(star(3), path(2)), "book3"))
    out.append(MG(product(star(4), path(3)), "K14xP3"))
    out.append(MG(product(star(3), star(3)), "K13xK13"))
    out.append(MG(product(random_tree(rng, 6), random_tree(rng, 5)), "T6xT5"))
    out.append(MG(product(product(star(3), path(2)), path(2)), "K13xP2xP2"))
    out.append(MG(product(product(path(3), path(3)), path(2)), "P3xP3xP2"))
    # RAAG hulls: P4 = a-b-c-d (0-1-2-3), K1*P4, triangle+pendant, C5
    P4 = [(0, 1), (1, 2), (2, 3)]
    a, b, c, d = [(i, 1) for i in range(4)]
    ai, bi, ci, di = [(i, -1) for i in range(4)]
    S = [(), (a, c), (b, d), (c, a, d), (d, b, ai), (a, b, ci, d)]
    out.append(raag_hull(4, P4, S, "P4-hull1")[0])
    S = [(), (a, c, a), (d, b, d), (c, d, ai)]
    out.append(raag_hull(4, P4, S, "P4-hull2")[0])
    K1P4 = P4 + [(4, i) for i in range(4)]
    e = (4, 1)
    S = [(), (a, e, c), (d, b), (e, e, a, d)]
    out.append(raag_hull(5, K1P4, S, "K1*P4-hull")[0])
    TP = [(0, 1), (1, 2), (0, 2), (2, 3)]
    S = [(), (a, b, d), (d, c, a), (b, d, b)]
    out.append(raag_hull(4, TP, S, "tri+pendant-hull")[0])
    C5 = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    S = [(), (a, c, e), (b, d), ((4, 1), b, (3, -1))]
    out.append(raag_hull(5, C5, S, "C5-hull")[0])
    for t in range(4 if not big else 10):
        adj = buneman(rng, rng.randint(4, 6), rng.randint(3, 6))
        out.append(MG(adj, "bun%d" % t))
    return out


if __name__ == "__main__":
    import sys
    for G in zoo(int(sys.argv[1]) if len(sys.argv) > 1 else 0):
        print(G.name, "n", G.n, "hyperplanes", G.m, "k", G.k, "maxcubes", len(G.maxcubes),
              "quadrants", len(G.Q), "median", G.median_ok, "hamming", G.hamming_ok, flush=True)
