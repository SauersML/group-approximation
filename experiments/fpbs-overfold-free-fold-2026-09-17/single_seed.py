"""Exhaustive single-seed free-fold scan (see freefold.py).

For random transitive L_{j+1}-sets of size d and EVERY seed pair of
Gamma_K with distinct C_{j+1}-labels, fold freely and test for a hit.
A hit with law >= 2 would refute (O) (deep <= 1 < law on that component).
Usage: python3 single_seed.py j d trials seed [maxlaw]
"""
import random
import sys
from collections import Counter
from freefold import core, cover, label, analyse


def transitive(al, ta):
    n = len(al)
    seen = {0}
    st = [0]
    ia = {v: i for i, v in enumerate(al)}
    it = {v: i for i, v in enumerate(ta)}
    while st:
        p = st.pop()
        for q in (al[p], ta[p], ia[p], it[p]):
            if q not in seen:
                seen.add(q)
                st.append(q)
    return len(seen) == n


def main():
    j, d, trials, seed = [int(x) for x in sys.argv[1:5]]
    maxlaw = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    rng = random.Random(seed)
    Cj, Cj1 = core(j), core(j + 1)
    iota = label(Cj1, Cj)
    tot = Counter()
    lawhist = Counter()
    done = 0
    while done < trials:
        al = list(range(d)); rng.shuffle(al)
        ta = list(range(d)); rng.shuffle(ta)
        if not transitive(al, ta):
            continue
        done += 1
        nbK = cover(al, ta, j + 1)
        assert len(nbK) == d * len(Cj1), (len(nbK), d, len(Cj1))
        lab = label(nbK, Cj1)
        V = len(nbK)
        best = 0
        for u in range(V):
            for v in range(u + 1, V):
                if lab[u] == lab[v]:
                    continue
                kind = 'law' if iota[lab[u]] == iota[lab[v]] else 'over'
                r = analyse(nbK, [(u, v)], Cj, Cj1, j, maxlaw)
                if r is None:
                    tot[kind, 'none'] += 1
                elif r[0] == 'infidx':
                    tot[kind, 'infidx'] += 1
                elif r[0] == 'nt':
                    tot[kind, 'intrans'] += 1
                else:
                    tot[kind, 'hit'] += 1
                    lawhist[kind, r[3]] += 1
                    if kind == 'over':
                        best = max(best, r[3] if r[3] is not None else 99)
                    if r[3] is None or r[3] >= 2:
                        print('FLAG', kind, 'alpha', al, 'tau', ta,
                              'seed', (u, v), 'labels', (lab[u], lab[v]), r)
        print('trial', done, 'alpha', al, 'tau', ta, 'V', V,
              'max law over overfold hits', best)
        sys.stdout.flush()
    print('totals', dict(tot))
    print('law histogram of hits', dict(lawhist))


if __name__ == '__main__':
    main()
