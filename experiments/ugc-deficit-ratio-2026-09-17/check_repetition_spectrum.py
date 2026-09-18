"""Numerical confirmation for parallel-repetition-collapses-threshold-rank-to-spectral-gap.

Builds a random bipartite weighted game G (multi-edges allowed), its n-fold
repetition G^n edge-tuple by edge-tuple, the constraint walk A(x,y)=w(x,y)/deg(x)
on V_L u V_R, and compares:
  * eigenvalues of A(G^n) above 0 with products of singular values of M(G);
  * r_gamma(G^n) == 1 if s_2 <= 1-gamma, and >= n*m + 1 otherwise.
Permutations do not affect the constraint walk, so they are omitted.
"""
import itertools
import random

import numpy as np


def random_game(rng, nl, nr):
    edges = []
    for u in range(nl):
        for _ in range(rng.randint(1, 3)):
            edges.append((u, rng.randrange(nr), rng.randint(1, 3)))
    for v in range(nr):  # no isolated right vertex
        edges.append((rng.randrange(nl), v, rng.randint(1, 3)))
    return edges


def walk_eigs(nl, nr, edges):
    n = nl + nr
    Wm = np.zeros((n, n))
    for u, v, w in edges:
        Wm[u, nl + v] += w
        Wm[nl + v, u] += w
    deg = Wm.sum(axis=1)
    S = Wm / np.sqrt(np.outer(deg, deg))
    return np.sort(np.linalg.eigvalsh(S))[::-1]


def repeat(nl, nr, edges, n):
    idxl = {t: i for i, t in enumerate(itertools.product(range(nl), repeat=n))}
    idxr = {t: i for i, t in enumerate(itertools.product(range(nr), repeat=n))}
    out = []
    for tup in itertools.product(edges, repeat=n):
        u = tuple(e[0] for e in tup)
        v = tuple(e[1] for e in tup)
        out.append((idxl[u], idxr[v], int(np.prod([e[2] for e in tup]))))
    return nl ** n, nr ** n, out


def main():
    rng = random.Random(20260918)
    checks = 0
    for _ in range(25):
        nl, nr = rng.randint(2, 4), rng.randint(2, 4)
        edges = random_game(rng, nl, nr)
        Wlr = np.zeros((nl, nr))
        for u, v, w in edges:
            Wlr[u, v] += w
        M = Wlr / np.sqrt(np.outer(Wlr.sum(axis=1), Wlr.sum(axis=0)))
        s = np.sort(np.linalg.svd(M, compute_uv=False))[::-1]
        assert abs(s[0] - 1) < 1e-9
        for n in (2, 3):
            if len(edges) ** n > 60000:
                continue
            L, R, rep = repeat(nl, nr, edges, n)
            ev = walk_eigs(L, R, rep)
            prods = np.sort([np.prod(t) for t in itertools.product(s, repeat=n)])[::-1]
            pos = ev[ev > 1e-7]
            assert np.allclose(pos, prods[prods > 1e-7][:len(pos)], atol=1e-7), (pos, prods)
            for _ in range(5):
                gamma = rng.uniform(0.01, 0.9)
                r = int(np.sum(ev > 1 - gamma + 1e-9))
                m = int(np.sum(s[1:] > 1 - gamma + 1e-9))
                if m == 0:
                    assert r == 1, (r, s, gamma)
                else:
                    assert r >= n * m + 1, (r, n, m)
                checks += 1
    print(f"OK: spectrum of repeated walks equals singular-value products; dichotomy held in {checks} tests")


if __name__ == "__main__":
    main()
