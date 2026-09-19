"""Vertex-simple R_s for n = 2, 3 with long labels, some built to fold.

Families (u, v random reduced words, k short elements of K):
  rand : h_i random of length 4..8, last label forced so a chain exists;
  fold : h_2 = v k u^-1 style labels whose middle cancels against h_1;
  pow  : h_i = w^j for a fixed short w outside K (periodic labels).
Each value is computed at two truncations L to check stability.
Usage: s3_long.py seed trials L1 L2
"""
import random, sys
from chains import k_elements, in_K, red, inv
from simple import R_s

seed, trials, L1, L2 = (int(x) for x in sys.argv[1:5])
random.seed(seed)
K1, K2 = k_elements(L1), k_elements(L2)
Ksh = [k for k in K1 if len(k) <= 4]
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def rword(n):
    w = ''
    while len(w) < n:
        x = random.choice('aAbB')
        if not (w and w[-1] == INV[x]):
            w += x
    return w


def ok(h):
    return h and not in_K(h) and len(h) <= 16


def sample(fam, n):
    if fam == 'pow':
        w = rword(random.choice([1, 2, 3]))
        return [red(w * random.choice([1, 2, 3])) for _ in range(n)]
    hs = [rword(random.choice([4, 5, 6])) for _ in range(n - 1)]
    if fam == 'fold':
        hs = [hs[0]] + [red(rword(2) + random.choice(Ksh) + inv(hs[0])[:3])
                        for _ in range(n - 2)]
    g = ''
    for h in hs:
        g = red(h + random.choice(Ksh) + g)
    last = red('b' + random.choice(Ksh) + inv(g))
    return hs + [last]


best, unstable, done = [], 0, 0
for t in range(trials):
    fam = random.choice(['rand', 'fold', 'pow'])
    n = 3
    hs = sample(fam, n)
    if not all(ok(h) for h in hs):
        continue
    r1, r2 = R_s(hs, K1), R_s(hs, K2)
    done += 1
    unstable += r1 != r2
    best.append((r2, r1, n, fam, tuple(hs)))
best.sort(reverse=True)
for b in best[:10]:
    print(b)
print('tested', done, 'unstable', unstable)
