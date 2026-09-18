"""Census over K of given rank, all transitive degree-d Schreier graphs N.

Usage: python3 run3.py maxlen dmax vmax limit ngen
Prints DROP lines and a histogram keyed by
(rank K, rmin K, d, rank(K cap N) - mrk_N(K cap N), search complete?).
"""
import itertools, sys, collections
from census import *
from run import words, canon_graph


def main(maxlen, dmax, vmax, limit, ngen):
    W = words(maxlen)
    seenK = set()
    drops = []
    stats = collections.Counter()
    for gens in itertools.combinations(W, ngen):
        K = stallings(list(gens))
        nv, E, base = K
        rk = rank(nv, E)
        if rk != ngen or nv > vmax:
            continue
        key = canon_graph(K)
        if key in seenK:
            continue
        seenK.add(key)
        rmin, _, _ = min_quotient_rank(nv, E, [list(range(nv))])
        for d in range(2, dmax + 1):
            for perms in covers(d):
                n, PE, b, col, trans = product(K, perms)
                if not trans:
                    continue
                classes = [[i for i in range(n) if col[i] == c] for c in range(d)]
                mrk, wit, complete = min_quotient_rank(n, PE, classes, limit)
                stats[(rk, rmin, d, rank(n, PE) - mrk, complete)] += 1
                fb = 1 + (mrk - 1) / d
                if fb < rmin - 1e-9:
                    drops.append(gens)
                    print('DROP', gens, d, perms, 'rmin', rmin, 'mrk', mrk,
                          'fb', fb, complete, flush=True)
    print('distinct K', len(seenK), 'drops', len(drops))
    for k in sorted(stats):
        print('rk,rmin,d,rankH-mrk,complete', k, stats[k])


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
