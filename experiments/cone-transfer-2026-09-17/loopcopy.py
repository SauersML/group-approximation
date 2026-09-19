"""Swap a loop P0 at A with a rotated copy Pj (same word, start j full turns later) that ends at B_j != A.
Records the excess change and the corner-count change.  Usage: python3 loopcopy.py SEED TRIALS L"""
import random, sys
from collections import Counter
from swap import Surf, excess, tori, perturb_local, apply_swap, vertices
from transfer import ccw, words
from fulltransfer import paths
seed, trials, L = map(int, sys.argv[1:4]); rng = random.Random(seed); tally = Counter()
for t in range(trials):
    n = rng.choice((6, 7, 8, 9)); b0, c0 = tori([(n, n)])
    b, c = perturb_local(b0, c0, rng.randrange(1, 6), rng, 3); S = Surf(b, c); E = excess(b, c)
    for A in S.cones():
        o = ccw(S, next((i // 4, i % 4) for i in S.cls[A])); M = len(o)
        for r0 in range(4):
            for j in range(1, M // 4):
                s0, sj = o[r0], o[r0 + 4 * j]
                for ell in range(L):
                    for w in words(ell):
                        P0, Pj = paths(S, [s0, sj], w)
                        if S.vend(P0[-1]) != A or S.vend(Pj[-1]) == A: continue
                        inner = [S.vend(st) for P in (P0, Pj) for st in P[:-1]]
                        if len(set(inner)) != len(inner) or set(inner) & {A, S.vend(Pj[-1])}: continue
                        r = apply_swap(S, P0, Pj)
                        if r is None: continue
                        Bj = S.vend(Pj[-1])
                        old = sorted(len(S.cls[v]) // 4 - 1 for v in (A, Bj))
                        new = Counter(len(cl) for cl in vertices(*r)[1].values()); oldc = Counter(len(cl) for cl in S.cls.values())
                        diff = tuple(sorted((k, new[k] - oldc[k]) for k in set(new) | set(oldc) if new[k] != oldc[k]))
                        tally[(excess(*r) - E, 'kA,kB', tuple(old), diff)] += 1
for k, v in sorted(tally.items(), key=str): print(k, v)
