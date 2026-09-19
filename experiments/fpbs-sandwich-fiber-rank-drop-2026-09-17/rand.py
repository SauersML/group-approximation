"""Random census: random K (ngen random reduced words), random transitive
degree-d covers N with K N = F_2. Records rank(K cap N) - mrk_N(K cap N)
against d*(rk K - rmin K), which is the value forced by the obvious
overgroup M cap N (M a least-rank overgroup of K).

Usage: python3 rand.py seed trials ngen maxlen dmin dmax vmax limit
"""
import random, sys, collections, itertools
from census import *


def rand_word(rng, L):
    w = ''
    while len(w) < L:
        c = rng.choice('aAbB')
        if w and INV[c] == w[-1]:
            continue
        w += c
    return w


def rand_cover(rng, d):
    while True:
        pa = list(range(d)); rng.shuffle(pa)
        pb = list(range(d)); rng.shuffle(pb)
        pa, pb = tuple(pa), tuple(pb)
        seen = {0}; st = [0]
        while st:
            x = st.pop()
            for p in (pa, pb):
                for y in (p[x], p.index(x)):
                    if y not in seen:
                        seen.add(y); st.append(y)
        if len(seen) == d:
            return (pa, pb)


def main(seed, trials, ngen, maxlen, dmin, dmax, vmax, limit):
    rng = random.Random(seed)
    stats = collections.Counter()
    drops = 0
    done = 0
    while done < trials:
        gens = [rand_word(rng, rng.randint(1, maxlen)) for _ in range(ngen)]
        K = stallings(gens)
        nv, E, base = K
        if rank(nv, E) != ngen or nv > vmax or nv < 2:
            continue
        rmin, _, _ = min_quotient_rank(nv, E, [list(range(nv))])
        d = rng.randint(dmin, dmax)
        perms = rand_cover(rng, d)
        n, PE, b, col, trans = product(K, perms)
        if not trans:
            continue
        classes = [[i for i in range(n) if col[i] == c] for c in range(d)]
        mrk, wit, complete = min_quotient_rank(n, PE, classes, limit)
        done += 1
        rH = rank(n, PE)
        forced = 1 + d * (rmin - 1)
        key = (ngen, rmin, d, 'mrk-forced=%d' % (mrk - forced), complete)
        stats[key] += 1
        if mrk < forced:
            drops += 1
            print('DROP', gens, perms, 'rmin', rmin, 'rankH', rH, 'mrk', mrk,
                  'forced', forced, complete, flush=True)
    print('trials', done, 'drops', drops)
    for k in sorted(stats, key=str):
        print(k, stats[k])


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
