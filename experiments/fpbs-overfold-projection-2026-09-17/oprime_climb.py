"""Adversarial search for violations of (O'-rel) (see oprime.py).

Hill-climbs over sets P of k level-0 seeds on random levels Q, maximising
the greedy upper bound g(P) for the level >= 1 seed number of
cl(P) ∩ ker p_1.  Any P with g(P) > |P| is re-checked exactly (exact seed
number over subsets of the contained blocks); only an exact value > |P| is a
violation.  Also records the best ratio g(P)/|P| seen (the "half" statistic).

Usage: python3 oprime_climb.py j n k levels restarts steps seed
"""
import itertools
import random
import sys
from oprime import level_maps, blocks_of, contained, greedy, exact, closure
from foldlib import random_q


def main():
    j, n, k, levels, restarts, steps, sd = map(int, sys.argv[1:8])
    rng = random.Random(sd)
    best_overall = (0, None)
    viol = 0
    for lv in range(levels):
        PA, PB = random_q(n, rng)
        G, maps = level_maps(PA, PB, j)
        m1 = maps[1]
        byfib = {}
        for v in range(G.V):
            byfib.setdefault(G.over[v], []).append(v)
        lvl0, hi = [], []
        for vs in byfib.values():
            for x, y in itertools.combinations(vs, 2):
                (hi if m1[x] == m1[y] else lvl0).append((x, y))
        if len(lvl0) < k:
            continue
        hib = blocks_of(G, hi)

        def score(P):
            B = contained(closure(G, P), hib)
            return (greedy(G, B) if B else 0), B
        lvbest = 0
        for _ in range(restarts):
            P = rng.sample(lvl0, k)
            s, B = score(P)
            for _ in range(steps):
                Q = list(P)
                Q[rng.randrange(k)] = rng.choice(lvl0)
                s2, B2 = score(Q)
                if s2 >= s:
                    P, s, B = Q, s2, B2
            if s > k:
                e = exact(G, B, k)
                if e is None:
                    viol += 1
                    print('VIOLATION PA', PA, 'PB', PB, 'P', P, flush=True)
            if s > lvbest:
                lvbest = s
                ex = exact(G, B, k)
        print('level', lv, 'best greedy seeds>=1 for k=%d level-0 seeds:' % k,
              lvbest, 'exact at that P:', ex, flush=True)
        if lvbest > best_overall[0]:
            best_overall = (lvbest, (PA, PB))
    print('max over levels', best_overall[0], 'k', k, 'violations', viol)


if __name__ == '__main__':
    main()
