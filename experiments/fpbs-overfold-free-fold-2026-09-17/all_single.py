"""Exhaustive single-seed free-fold scan over ALL transitive L_{j+1}-sets
of size d (up to isomorphism), with the realizability condition.

A seed g on Gamma_K is realizable in some finite Q with this base component
only if J = <K, g> satisfies J cap L_{j+1} = K (since J <= S and
S cap L_{j+1} = K); so d1 := [L_{j+1} : J cap L_{j+1}] must equal d.
A realizable seed is a hit iff J cap L_j has finite index d (then it is K').
(The earlier random scans single_seed.py did not impose d1 = d; their
overfold 'hits' all had d1 = 1, i.e. were not realizable.)
Counts per kind (lawful / overfold): realizable, hit; law histogram of hits.
FLAG = overfold hit with law >= 2 (deep <= 1 < law: refutes (O)).
Usage: python3 all_single.py j d [maxlaw]
"""
import sys
from collections import Counter
from freefold import (core, cover, label, fold_with, cover_degree,
                      transported_set, law0)
from bfs_free import classes


def main():
    j, d = int(sys.argv[1]), int(sys.argv[2])
    maxlaw = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    Cj, Cj1 = core(j), core(j + 1)
    iota = label(Cj1, Cj)
    tot = Counter()
    lawhist = Counter()
    ncl = 0
    nflag = 0
    for al, ta in classes(d):
        ncl += 1
        nbK = cover(al, ta, j + 1)
        lab = label(nbK, Cj1)
        V = len(nbK)
        for u in range(V):
            for v in range(u + 1, V):
                if lab[u] == lab[v]:
                    continue
                kind = 'law' if iota[lab[u]] == iota[lab[v]] else 'over'
                nbH = fold_with(nbK, [(u, v)])
                d1, _, _ = cover_degree(nbH, Cj1)
                if d1 != d:
                    tot[kind, 'unrealizable'] += 1
                    continue
                tot[kind, 'realizable'] += 1
                d0, order, adj = cover_degree(nbH, Cj)
                if d0 != d:
                    continue
                tot[kind, 'hit'] += 1
                PA, PB = transported_set(order, adj, j)
                lw = law0(PA, PB, maxlaw)
                lawhist[kind, lw] += 1
                if kind == 'over' and (lw is None or lw >= 2):
                    nflag += 1
                    print('FLAG alpha', al, 'tau', ta, 'seed', (u, v),
                          'law', lw, 'P', PA, PB)
                    sys.stdout.flush()
    print('j', j, 'd', d, 'classes', ncl, 'flags', nflag)
    print('totals', sorted(tot.items()))
    print('law histogram of hits', sorted(lawhist.items(), key=str))


if __name__ == '__main__':
    main()
