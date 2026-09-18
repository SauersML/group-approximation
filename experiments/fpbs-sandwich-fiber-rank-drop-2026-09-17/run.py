import itertools, sys
from census import *


def words(maxlen):
    out = ['']
    for L in range(1, maxlen + 1):
        for t in itertools.product('aAbB', repeat=L):
            w = ''.join(t)
            if reduce(w) == w:
                out.append(w)
    return out[1:]


def canon_graph(G):
    nv, E, base = G
    return (nv, tuple(E), base)


def main(maxlen=4, dmax=3, vmax=5, limit=400000):
    W = words(maxlen)
    seenK = set()
    drops = []
    ntested = 0
    for u, v in itertools.combinations(W, 2):
        K = stallings([u, v])
        nv, E, base = K
        if rank(nv, E) != 2 or nv > vmax:
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
                    continue  # K not transitive on F_2/N
                rH = rank(n, PE)
                assert rH == 1 + d * (2 - 1), (u, v, perms, rH)
                classes = [[i for i in range(n) if col[i] == c] for c in range(d)]
                mrk, wit, complete = min_quotient_rank(n, PE, classes, limit)
                ntested += 1
                fb = 1 + (mrk - 1) / d
                if fb < rmin - 1e-9:
                    drops.append((u, v, d, perms, rmin, mrk, fb, complete))
                    print('DROP', u, v, d, perms, 'rmin', rmin, 'mrk', mrk,
                          'fiber bound', fb, 'complete' if complete else 'partial', flush=True)
    print('distinct K', len(seenK), 'pairs (K,N) tested', ntested, 'drops', len(drops))


if __name__ == '__main__':
    args = [int(x) for x in sys.argv[1:]]
    main(*args)
