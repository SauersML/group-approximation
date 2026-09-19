"""Sanity check of the transport identity used in freefold.py:
for an L_{j+1}-transitive L-set Q, law_j(Q) = law_0(P) where P is Q with
a acting as a and b acting as t_j.  Usage: python3 check_law0.py n j trials
"""
import random
import sys
from freefold import law0  # noqa: E402 (sets sys.path)
from foldlib import act, inverse_perm, t, A, depth_graphs, random_q
from multiorbit import comps, law_by_component
from struct_search import seeds_of


def main():
    n, j, trials = [int(x) for x in sys.argv[1:4]]
    rng = random.Random(7)
    done = bad = 0
    while done < trials:
        PA, PB = random_q(n, rng)
        Gj, G, m = depth_graphs(PA, PB, j)
        if len(set(comps(G))) != 1:
            continue  # need L_{j+1}-transitive (connected Gamma_{j+1})
        done += 1
        allp, lawp = seeds_of(G, m)
        lawj = law_by_component(G, Gj, m, lawp, 6)
        IA, IB = inverse_perm(PA), inverse_perm(PB)
        QA = [act(p, A, PA, PB, IA, IB) for p in range(n)]
        QB = [act(p, t(j), PA, PB, IA, IB) for p in range(n)]
        l0 = law0(QA, QB, 6)
        if l0 != lawj:
            bad += 1
            print('MISMATCH', PA, PB, lawj, l0)
        print(n, j, 'law_j', lawj, 'law_0(P)', l0)
    print('mismatches', bad, 'of', done)


if __name__ == '__main__':
    main()
