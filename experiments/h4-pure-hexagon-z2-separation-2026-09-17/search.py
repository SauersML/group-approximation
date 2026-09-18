"""Upward-flag search in the A_3 arc model.

x-vertices: arcs from t (puncture 3) to d0 (pure: braid fixes t).  A y-vertex adjacent to all given x-arcs exists
iff some puncture among q,a,b (0,1,2) lies in the region of D minus the arcs that contains d1.
Search for triples of distinct x-arcs, each pair having a common y, the triple having none.
Run: PYTHONPATH=. python3 search.py [nbraids] [maxlen] [seed]"""
import random, sys, itertools
from arcs import xarc, tight
import curver

from arcs import N
S = curver.load(0, N + 3)
X0 = S.arcs["s_%d" % N]
_cv = {}


def cvarc(braid):
    k = tuple(braid)
    if k not in _cv:
        h = S('.'.join(('s_%d' if g > 0 else 'S_%d') % abs(g) for g in braid)) if braid else S('')
        _cv[k] = h(X0)
    return _cv[k]


def outer(items):
    """items: list of (braid, Arc). punctures of {q,a,b} in the d1 region, from a placement whose pairwise
    crossing numbers equal curver's intersection numbers (None if the hill-climb fails)"""
    arcs = [A for _, A in items]
    target = {(a, b): cvarc(items[a][0]).intersection(cvarc(items[b][0]))
              for a in range(len(items)) for b in range(a + 1, len(items))}
    P = tight(arcs, target)
    if P is None:
        return None
    r = P.regions([("P", k) for k in range(N - 1)] + ["d1"])
    return frozenset(p for p in range(N - 1) if r[p] == r[N - 1])


def gen(n, L, seed):
    rng = random.Random(seed)
    seen = {}
    while len(seen) < n:
        b = [rng.choice([g for g in range(-N + 1, N) if g]) for _ in range(rng.randint(1, L))]
        A = xarc(b)
        if A.end != ("P", N - 1):
            continue
        key = A.word
        if key and key not in seen:
            seen[key] = (b, A)
    return list(seen.values())


def main(n=60, L=8, seed=1):
    from arcs import Arc
    g0 = Arc('d0', (), ("P", N - 1))
    cand = gen(n, L, seed)
    arcs = [([], g0)] + cand
    m = len(arcs)
    pair = {}
    for i, j in itertools.combinations(range(m), 2):
        pair[(i, j)] = outer([arcs[i], arcs[j]])
    good = [(i, j) for (i, j), s in pair.items() if s]
    print('undetermined pairs', sum(1 for s in pair.values() if s is None))
    print('arcs', m, 'pairs with common y', len(good), 'of', len(pair))
    found = 0
    undet = 0
    for i, j, k in itertools.combinations(range(m), 3):
        if pair[(i, j)] and pair[(j, k)] and pair[(i, k)]:
            s = outer([arcs[i], arcs[j], arcs[k]])
            if s is None:
                undet += 1
                continue
            if not s:
                found += 1
                if found <= 10:
                    print('CENTRELESS', [arcs[x][0] for x in (i, j, k)], [arcs[x][1].word for x in (i, j, k)],
                          'pairs', sorted(pair[(i, j)]), sorted(pair[(j, k)]), sorted(pair[(i, k)]))
    print('centreless triples', found, 'undetermined', undet)


if __name__ == '__main__':
    a = sys.argv[1:]
    main(int(a[0]) if a else 60, int(a[1]) if len(a) > 1 else 8, int(a[2]) if len(a) > 2 else 1)
