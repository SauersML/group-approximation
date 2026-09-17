"""Heuristic search in G=<lambda(C_n*C_n), s> <= V_(h,2)(<a>) for
nontrivial elements of small support, especially carry-free cone
permutations (candidates for cone 3-cycles / transpositions).

usage: python3 search_small_support.py n rounds seed
"""
import random, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from odom import *

n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
rounds = int(sys.argv[2]) if len(sys.argv) > 2 else 200
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
random.seed(seed)
h, gens, s = make_generators(n)
S = list(gens.values()) + [s, inverse(s, h)]
pool = []
# seed pool: localized odometer pairs and short words
cx = [comm(gens[(0, a)], power(s, 2 * h, h), h) for a in range(1, n)]
pool.extend(cx)
pool.extend(S)
def key(F):
    return (support_measure(F, h), len(F))
def carry_free(F):
    return all(k == 0 for (_, k) in F.values())
seen = set()
best = []
for r in range(rounds):
    f = random.choice(pool)
    g = random.choice(pool)
    if random.random() < 0.5:
        w = random.choice(S)
        g = compose(compose(w, g, h), inverse(w, h), h)
    c = comm(f, g, h)
    if is_id(c) or len(c) > 400:
        continue
    fs = fmt(c)
    if fs in seen:
        continue
    seen.add(fs)
    pool.append(c)
    if len(pool) > 300:
        pool.sort(key=key)
        pool = pool[:150] + S
    if carry_free(c):
        best.append((key(c), fs))
best.sort()
for kk, fs in best[:15]:
    print(kk, fs[:300])
