"""Sanity checks for the folding model.
1. Odometer Q = Z/N, a: +1, b: +k.  Relative cost is 0 on odometer
   products, so d(Q) should stay bounded as N grows.
2. Exhaustive single-merge test: is d(Q) = 1 for small random Q?
"""
import random
from fold import build_gamma_k, random_perm, ncls, k_orbits
from greedy import clone, greedy


def odometer(N, k):
    return [(x + 1) % N for x in range(N)], [(x + k) % N for x in range(N)]


def single_merge_collapses(PA, PB):
    F = build_gamma_k(PA, PB)
    n = len(PA)
    roots = sorted(F.roots())
    over = {}
    for r in roots:
        over.setdefault(F.phi[r], []).append(r)
    for p, L in over.items():
        for i in range(len(L)):
            for j in range(i + 1, len(L)):
                G = clone(F)
                G.merge(L[i], L[j])
                if ncls(G) == n:
                    return True
    return False


if __name__ == '__main__':
    rng = random.Random(3)
    for N, k in [(30, 0), (30, 1), (30, 7), (101, 5), (400, 13)]:
        PA, PB = odometer(N, k)
        d, gains = greedy(PA, PB, rng, 40)
        print('odometer', N, k, 'Korbits', k_orbits(PA, PB), 'd', d)
    for n in [8, 12, 20, 40, 80]:
        hits = 0; tr = 0
        for t in range(10):
            PA = random_perm(n, rng); PB = random_perm(n, rng)
            if k_orbits(PA, PB) != 1:
                continue
            tr += 1
            hits += single_merge_collapses(PA, PB)
        print('single-merge d=1', n, hits, '/', tr)
