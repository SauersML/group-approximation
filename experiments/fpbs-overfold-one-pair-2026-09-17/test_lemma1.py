"""Check Lemma 1 on random data: every <X,g> is an arc extension of Gamma_X or
one of the one-pair folds fold(Gamma_X / u~w)."""
import random, sys
from folding import *

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
assert is_rose(*graph_of(['a', 'b']))
n1, E1 = graph_of(['a', phi('b')])
print('C_1:', n1, E1)
bad = arcs = pairs = 0
T = 3000
for trial in range(T):
    X = [rand_word(rng.randint(1, 6), rng) for _ in range(rng.randint(2, 4))]
    n, E = graph_of(X)
    if rank(n, E) < 2:
        continue
    g = rand_word(rng.randint(1, 12), rng)
    J = canon(*graph_of(X + [g]))
    one = {canon(*fold(n, E, [(u, w)])[:2]) for u in range(n) for w in range(n)}
    if J in one:
        pairs += 1
    else:
        m, EJ = graph_of(X + [g])
        if rank(m, EJ) == rank(n, E) + 1:
            arcs += 1
        else:
            bad += 1
            print('BAD', X, g)
print('pairs', pairs, 'arcs', arcs, 'bad', bad)
