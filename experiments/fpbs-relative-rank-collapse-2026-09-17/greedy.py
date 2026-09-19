"""Greedy merge search: an upper bound on d(Q) = least number of chord edges
(of any length) that, with K = <a, bab^-2>, generate E_L on every free
cover of the finite L-set Q.  Each chord that folds completely is one merge
of two vertices u, u' of the folded K-graph with phi(u) = phi(u').
Candidates: extra-with-real and extra-with-extra pairs over one point.
"""
import random, sys
from collections import defaultdict
from fold import Folder, build_gamma_k, random_perm, ncls


def clone(F):
    G = Folder()
    G.par = F.par[:]
    G.out = [dict(d) for d in F.out]
    G.phi = F.phi
    G.real = F.real[:]
    return G


def candidates(F, rng, k):
    over = defaultdict(list)
    for r in F.roots():
        over[F.phi[r]].append(r)
    pts = [p for p, L in over.items() if len(L) > 1]
    out = []
    for _ in range(k):
        p = rng.choice(pts)
        L = over[p]
        u, v = rng.sample(L, 2)
        out.append((u, v))
    return out


def greedy(PA, PB, rng, k=60):
    F = build_gamma_k(PA, PB)
    n = len(PA)
    d = 0
    gains = []
    while ncls(F) > n:
        best = None
        base = ncls(F)
        for (u, v) in candidates(F, rng, k):
            G = clone(F)
            G.merge(u, v)
            g = base - ncls(G)
            if best is None or g > best[0]:
                best = (g, G)
        F = best[1]
        d += 1
        gains.append(best[0])
    return d, gains


if __name__ == '__main__':
    n = int(sys.argv[1]); trials = int(sys.argv[2]); k = int(sys.argv[3])
    rng = random.Random(7)
    for t in range(trials):
        PA = random_perm(n, rng); PB = random_perm(n, rng)
        d, gains = greedy(PA, PB, rng, k)
        print(n, t, 'd', d, 'd/n %.4f' % (d / n), 'first gains', gains[:10], 'max', max(gains))
