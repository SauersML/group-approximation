# Calibration of the H_1 disc invariant against the closed-form braid monodromy (w18-042).
# For random pure Artin words g, the loop L(g) gives a pure 46-braid; its exponent sums e_ij give
# iota(L(g).Delta_F) in Z^84.  Every such vector must lie in span(Lambda) (they are in mu^(P°)).
import sys, random, numpy as np, itertools
sys.path.insert(0, sys.path[0])
exec(open(sys.path[0] + '/lattice.py').read().split('# ---- gluing')[0].replace("name = sys.argv[1] if len(sys.argv) > 1 else 'H4'", "name = 'H4'"))
from mono import Arr as Arr2

def expo(A2, word):
    bw, winv, _ = A2.braid(word)
    order = list(A2.order0); E = {}
    for k, e in bw:
        l, r = order[k], order[k + 1]
        E[(min(l, r), max(l, r))] = E.get((min(l, r), max(l, r)), 0) + e
        order[k], order[k + 1] = r, l
    assert np.allclose(winv, np.eye(4)), 'word not pure'
    assert all(v % 2 == 0 for v in E.values())
    return {p: v // 2 for p, v in E.items()}

def iota(E):
    v = [0] * (2 * len(out))
    g = lambda a, j: E.get((min(a, j), max(a, j)), 0)
    for t, j in enumerate(out):
        v[2 * t] = g(Fi[0], j) - g(Fi[2], j); v[2 * t + 1] = g(Fi[1], j) - g(Fi[2], j)
    return Matrix([v])

A2 = Arr2('H4'); rng = random.Random(5)
gens = []
for i in range(1, 5):   # standard pure generators w s_i^2 w^-1 with short w
    for w in [[], [1], [2], [3], [4], [1, 2], [2, 3], [3, 4], [4, 3], [3, 2], [2, 1], [2, 3, 4], [4, 3, 2]]:
        if i in w[-1:]: continue
        gens.append(w + [i, i] + [-x for x in reversed(w)])
rk = M.rank(); bad = 0; tot = 0
for trial in range(60):
    word = sum((rng.choice(gens) if rng.random() < .5 else [-x for x in reversed(rng.choice(gens))]
                for _ in range(rng.randint(1, 4))), [])
    try: v = iota(expo(A2, word))
    except AssertionError as e: print('skip', e); continue
    tot += 1
    if Matrix.vstack(M, v).rank() > rk: bad += 1; print('OUTSIDE span(Lambda):', word)
print('calibration: %d words, %d outside span(Lambda)' % (tot, bad))
