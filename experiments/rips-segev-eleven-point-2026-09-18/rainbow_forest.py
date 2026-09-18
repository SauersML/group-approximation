"""Calibration for rips-segev-steenbock-eleven-point-a-supports-are-regular.

Steenbock's row r has distinguished positions {0, 10^(5r-4), ..., 10^(5r)}.
Dist_r = nonzero differences of two of them.  For a finite S of integers,
L_S = set of rows r with (S - S) meeting Dist_r.  Claim: |L_S| <= |S| - 1.

Checks:
 1. Rows are super-increasing: min Dist_r^+ > sum_{r'<r} max Dist_r'^+.
 2. Rips--Segev condition: all positive differences over all rows are distinct.
 3. Random S built to hit many rows (random walks by Dist steps, random
    unions, and adversarial "closing" attempts): |L_S| <= |S| - 1 always.
 4. Sharpness: S = partial sums of 11 steps on 11 distinct rows gives
    |S| = 12 and |L_S| = 11.
Usage: python3 rainbow_forest.py [seed]
"""
import random, sys, itertools

R = 40
def positions(r):
    return [0] + [10 ** e for e in range(5 * r - 4, 5 * r + 1)]
DIST = {}
for r in range(1, R + 1):
    p = positions(r)
    for x, y in itertools.combinations(p, 2):
        d = abs(x - y)
        assert d not in DIST, "RS condition violated"
        DIST[d] = r
rows_min = {r: min(d for d, rr in DIST.items() if rr == r) for r in range(1, R + 1)}
rows_max = {r: max(d for d, rr in DIST.items() if rr == r) for r in range(1, R + 1)}
for r in range(2, R + 1):
    assert rows_min[r] > sum(rows_max[s] for s in range(1, r)), r
print("super-increasing rows and RS condition: ok for rows 1..%d" % R)

def L(S):
    out = set()
    for x, y in itertools.combinations(S, 2):
        r = DIST.get(abs(x - y))
        if r is not None:
            out.add(r)
    return out

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = random.Random(seed)
dlist = sorted(DIST)
worst = 0
trials = 0
for t in range(20000):
    m = rng.randint(2, 14)
    mode = rng.random()
    S = {0}
    while len(S) < m:
        if mode < 0.5:   # random walk from a random existing point
            base = rng.choice(sorted(S))
        else:            # try to close cycles: step from point, then also try hitting another point
            base = rng.choice(sorted(S))
        rs = rng.sample(range(1, 13), 1)[0]
        cand = [d for d in dlist if DIST[d] == rs]
        S.add(base + rng.choice([1, -1]) * rng.choice(cand))
        if mode >= 0.5 and len(S) < m:
            # add a point at a Dist-distance from two existing points if possible
            pts = sorted(S)
            x, y = rng.sample(pts, 2) if len(pts) > 1 else (pts[0], pts[0])
            for d in rng.sample(cand, len(cand)):
                z = x + d
                if abs(z - y) in DIST:
                    S.add(z)
                    break
    S = sorted(S)
    trials += 1
    l = len(L(S))
    assert l <= len(S) - 1, (S, L(S))
    worst = max(worst, l - (len(S) - 1))
print("random sets: %d, max of |L_S| - (|S|-1) = %d (<= 0 required)" % (trials, worst))

# sharpness: 11 steps on rows 1..11 in random order and random Dist element
rows = list(range(1, 12)); rng.shuffle(rows)
S = [0]
for r in rows:
    cand = [d for d in dlist if DIST[d] == r]
    S.append(S[-1] + rng.choice([1, -1]) * rng.choice(cand))
print("sharpness: |S| = %d, |L_S| = %d" % (len(set(S)), len(L(S))))
