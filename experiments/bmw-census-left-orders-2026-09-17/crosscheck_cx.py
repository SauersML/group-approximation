# Brute-force check of cxmn.enumerate_normalized: over all P[1..m-1] in S_n and Q[1..n-1] in S_m (P[0] = Q[0] = id),
# keep the data whose pairs (v1,h1) are all distinct, and compare with the backtracker.  Also checks that the class
# representatives of census_cx_{m}{n}.json have pairwise disjoint orbits covering every normalized datum.
import itertools, json, sys
from cxmn import enumerate_normalized, orbit, normalized
for m, n in ((3, 3), (3, 4)):
    pn = list(itertools.permutations(range(n))); pm = list(itertools.permutations(range(m)))
    brute = set()
    for Pr in itertools.product(pn, repeat=m - 1):
        P = (tuple(range(n)),) + Pr
        for Qr in itertools.product(pm, repeat=n - 1):
            Q = (tuple(range(m)),) + Qr
            S = [(h0, P[h0][w], Q[w][h0], w) for h0 in range(m) for w in range(n)]
            if len({(s[1], s[2]) for s in S}) == m * n: brute.add(tuple(sorted(S)))
    bt = enumerate_normalized(m, n); assert len(bt) == len(set(bt)) and set(bt) == brute
    reps = [tuple(map(tuple, r)) for r in json.load(open(f'census_cx_{m}{n}.json'))['reps']]
    cover = [{x for x in orbit(r, m, n) if normalized(x, m, n)} for r in reps]
    assert sum(len(c) for c in cover) == len(brute) and set().union(*cover) == brute
    print(f'({m},{n}): normalized data {len(brute)} (brute force = backtracker), {len(reps)} classes, orbits partition the data')
