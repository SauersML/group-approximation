"""Structure of single overfold-seed hits: ranks and embedding of Gamma_{K'}.
Prints counts keyed by (d_{j+1}, d_j, rk H - rk K', Gamma_{K'} -> Gamma_H
injective on vertices, |V Gamma_H|, |V Gamma_{K'}|).
Usage: python3 probe_hits.py j d trials seed
"""
import random
import sys
from collections import Counter
from freefold import core, cover, label, fold_with, cover_degree
from single_seed import transitive


def main():
    j, d, trials, seed = [int(x) for x in sys.argv[1:5]]
    rng = random.Random(seed)
    Cj, Cj1 = core(j), core(j + 1)
    iota = label(Cj1, Cj)
    stats = Counter()
    done = 0
    while done < trials:
        al = list(range(d)); rng.shuffle(al)
        ta = list(range(d)); rng.shuffle(ta)
        if not transitive(al, ta):
            continue
        done += 1
        nbK = cover(al, ta, j + 1)
        lab = label(nbK, Cj1)
        for u in range(len(nbK)):
            for v in range(u + 1, len(nbK)):
                if lab[u] == lab[v] or iota[lab[u]] == iota[lab[v]]:
                    continue
                nbH = fold_with(nbK, [(u, v)])
                d0, order, adj = cover_degree(nbH, Cj)
                if d0 is None:
                    continue
                d1, _, _ = cover_degree(nbH, Cj1)
                E = sum(len(x) for x in nbH) // 2
                rkH = E - len(nbH) + 1
                img = {h for (h, c) in order}
                stats[(d1, d0, rkH - (d0 + 1), len(img) == len(order),
                       len(nbH), len(order))] += 1
    for k, v in sorted(stats.items()):
        print(k, v)


if __name__ == '__main__':
    main()
