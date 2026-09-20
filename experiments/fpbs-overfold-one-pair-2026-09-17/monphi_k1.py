"""Exact test of (Mon_phi) at k = 1, i.e. E(2) for Y = L_1, and of (W).

For random X_0 <= F (rank >= 2):
  A := some g in F has <phi X_0, g> = F   (exact: one-pair folds of Gamma_{phi X_0})
  B := some h in F has <X_0, h> = F       (exact: one-pair folds of Gamma_{X_0})
  W := <X_0, a> = F or <X_0, b> = F
A and not B is a counterexample to (Mon_phi) at k=1 (so to E(2) for L_1).
A and not W is a counterexample to (W).
No bound on the length of g or h is involved (Lemma 1).
usage: monphi_k1.py seed trials maxgens maxlen
"""
import random, sys
from folding import *

seed, T, G, Lm = (int(x) for x in sys.argv[1:5])
rng = random.Random(seed)
stats = dict(tot=0, A=0, B=0, AnotB=0, AnotW=0, BnotA=0, W=0)
for trial in range(T):
    X0 = [rand_word(rng.randint(1, Lm), rng) for _ in range(rng.randint(2, G))]
    n0, E0 = graph_of(X0)
    if rank(n0, E0) < 2:
        continue
    X = [phi(w) for w in X0]
    n, E = graph_of(X)
    stats['tot'] += 1
    A = bool(one_pair_to_rose(n, E))
    B = bool(one_pair_to_rose(n0, E0))
    W = is_rose(*graph_of(X0 + ['a'])) or is_rose(*graph_of(X0 + ['b']))
    stats['A'] += A
    stats['B'] += B
    stats['W'] += W
    if A and not B:
        stats['AnotB'] += 1
        print('MONPHI-VIOLATION', X0, flush=True)
    if A and not W:
        stats['AnotW'] += 1
        print('W-VIOLATION', X0, flush=True)
    if B and not A:
        stats['BnotA'] += 1
print(stats)
