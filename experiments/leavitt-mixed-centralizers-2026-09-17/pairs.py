"""Pair census: for random small mixed-degree a in L_{F_2}(1,2) with a transcendental
(no relation among 1, a, ..., a^D), take the centralizer C_R(a) in the window
|w|, |v| <= R and test every basis element b of C_R(a) and random sums of two of them:
is the commuting pair (a, b) dependent?  We report the rank of the monomials
a^i b^j (0 <= i, j <= N) against (N+1)^2.  A full-rank pair would be a candidate for
k[x, y] inside L; every rank deficit is a certified polynomial relation of
bidegree <= (N, N).

With the fifth argument 'residual', only elements a whose bidegree cone meets both closed
quadrants are used.  Those are the elements not covered by
leavitt-weighted-halves-have-dependent-commuting-pairs.

Run: python3 pairs.py [num_a] [seed] [R] [N] [residual]
"""
import sys, random
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from leavitt import window, centralizer, mul, add, ONE, degrees


def rank_F2(elts):
    index, pivots, r = {}, {}, 0
    for e in elts:
        row = 0
        for key in e:
            row ^= 1 << index.setdefault(key, len(index))
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                r += 1
                break
    return r


def powers(a, n):
    out = [ONE]
    for _ in range(n):
        out.append(mul(out[-1], a))
    return out


def pair_rank(a, b, N):
    pa, pb = powers(a, N), powers(b, N)
    return rank_F2([mul(x, y) for x in pa for y in pb])


def bidegrees(A):
    return {(w.count('0') - v.count('0'), w.count('1') - v.count('1')) for w, v in A}


def meets_both_quadrants(S):
    """True iff cone(S) meets both closed quadrants Q_+ and Q_- outside 0, i.e. S is
    residual for leavitt-weighted-halves-have-dependent-commuting-pairs.  cone(S) misses
    Q_- iff some integer weight (p, q) >= 1 is >= 0 on S; test weights up to 40."""
    def half(sign):
        return any(all(sign * (p * m + q * n) >= 0 for m, n in S)
                   for p in range(1, 41) for q in range(1, 41))
    return not half(1) and not half(-1)


def main():
    num = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    R = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    N = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    residual_only = len(sys.argv) > 5 and sys.argv[5] == 'residual'
    D = 8
    rng = random.Random(seed)
    W2 = window(2)
    tried = seen = 0
    best = 0
    done = set()
    while tried < num:
        a = frozenset(rng.sample(W2, rng.randint(2, 4)))
        d = degrees(a)
        if not (d[0] < 0 < d[-1]) or a in done:
            continue
        done.add(a)
        if residual_only and not meets_both_quadrants(bidegrees(a)):
            continue
        if rank_F2(powers(a, D)) < D + 1:
            continue  # algebraic of degree <= D
        tried += 1
        C = centralizer(a, R)
        cands = list(C) + [add(rng.choice(C), rng.choice(C)) for _ in range(len(C))]
        worst = 0
        for b in cands:
            if not b:
                continue
            r = pair_rank(a, b, N)
            worst = max(worst, r)
        best = max(best, worst)
        print(sorted(a), 'deg', d, 'dim C_R', len(C), 'max pair rank', worst, '/', (N + 1) ** 2)
    print('transcendental a tried', tried, 'overall max rank', best, '/', (N + 1) ** 2)


if __name__ == '__main__':
    main()
