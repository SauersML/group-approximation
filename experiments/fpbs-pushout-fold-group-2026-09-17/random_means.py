#!/usr/bin/env python3
"""Empirical mean of Z_S(V) = |Hom(P_V, S)| over uniformly random levels.

(b, c) independent uniform permutations of range(n), no conditioning (Theorem C
is about this model); also reports the fraction of samples on which K is
transitive.  Theorem C predicts E Z_S <= (n+1)^(|S|^2+2|S|); the census shows
E Z_S is in fact bounded in n.
"""
import random, sys, math
sys.path.insert(0, '.')
from foldgroup import *

rng = random.Random(4242)
G = small_groups()
ABEL = len(sys.argv) > 1 and sys.argv[1] == 'abelian'
for n in ([64, 128, 256] if ABEL else [8, 16, 32]):
    samples = 40 if n <= 64 else 20
    sums = {k: 0 for k in (['C2', 'C3'] if ABEL else ['C2', 'C3', 'S3'])}
    mx = {k: 0 for k in sums}
    ktrans = 0
    for _ in range(samples):
        Pb = list(range(n)); rng.shuffle(Pb)
        Pc = list(range(n)); rng.shuffle(Pc)
        Pb, Pc = tuple(Pb), tuple(Pc)
        ktrans += (k_orbits(Pb, Pc) == 1)
        tr = triples(Pb, Pc)
        r, R = (0, []) if ABEL else greedy_percolation(tr, n, rng, trials=4, want_set=True)
        for k in sums:
            mul, inv, one = table(G[k])
            if k in ('C2', 'C3'):
                p = len(mul)
                Z = p ** (n - rank_mod_p(tr, n, p))
            else:
                Z = count_colorings(tr, n, mul, inv, cap=10**6, seeds=R)
            sums[k] += Z; mx[k] = max(mx[k], Z)
    print(f"n={n:4d} samples={samples} P(K transitive)~{ktrans/samples:.2f}  " +
          "  ".join(f"mean Z_{k}={sums[k]/samples:.2f} (max {mx[k]})" for k in sums),
          flush=True)
