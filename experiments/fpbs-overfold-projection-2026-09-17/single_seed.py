"""Check of (Z1) for |P| = 1: a single level-0 seed s never folds a level >= 1
pair, i.e. cl(s) ∩ ker p_1 is trivial.

For each random Q (random permutations PA, PB of n points), every level-0
same-fibre seed of Gamma_{j+1}(Q) is tested.  Counts are split by whether
<a, b> acts transitively on Q.  Prints each failure.

Usage: python3 single_seed.py j nmin nmax trials seed
"""
import itertools
import random
import sys
from oprime import level_maps
from foldlib import closure, random_q


def transitive(PA, PB):
    n = len(PA)
    seen, st = {0}, [0]
    IA = [0] * n
    IB = [0] * n
    for i in range(n):
        IA[PA[i]] = i
        IB[PB[i]] = i
    while st:
        x = st.pop()
        for y in (PA[x], PB[x], IA[x], IB[x]):
            if y not in seen:
                seen.add(y)
                st.append(y)
    return len(seen) == n


def main():
    j, nmin, nmax, trials, sd = map(int, sys.argv[1:6])
    rng = random.Random(sd)
    stats = {True: [0, 0], False: [0, 0]}
    for _ in range(trials):
        n = rng.randint(nmin, nmax)
        PA, PB = random_q(n, rng)
        tr = transitive(PA, PB)
        G, maps = level_maps(PA, PB, j)
        m1 = maps[1]
        byfib = {}
        for v in range(G.V):
            byfib.setdefault(G.over[v], []).append(v)
        for vs in byfib.values():
            for x, y in itertools.combinations(vs, 2):
                if m1[x] == m1[y]:
                    continue
                cls = closure(G, [(x, y)])
                bad = any(cls[u] == cls[w] and m1[u] == m1[w]
                          for us in byfib.values()
                          for u, w in itertools.combinations(us, 2))
                stats[tr][0] += 1
                if bad:
                    stats[tr][1] += 1
                    print('FAIL transitive=%s PA %s PB %s seed %s'
                          % (tr, PA, PB, (x, y)), flush=True)
    for tr in (True, False):
        print('transitive=%s seeds tested %d failures %d'
              % (tr, stats[tr][0], stats[tr][1]))


if __name__ == '__main__':
    main()
