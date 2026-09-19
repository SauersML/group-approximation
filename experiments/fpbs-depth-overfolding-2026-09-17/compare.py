"""Exact law_j(Q) against heuristic upper bounds for deep_j(Q).

law_j(Q): least set of lawful seeds (indexed by points of Q) whose fold
closure equals ker; exact, by increasing subset size.
deep upper bound: best of R restarts of greedy (pick the seed that most
increases the number of ker-pairs already merged, ties random) then prune.
A deep bound below law refutes overfold domination (O) at this Q.
Usage: python3 compare.py n j trials seed restarts
"""
import itertools
import random
import sys
from foldlib import random_q, closure, contains_kernel
from seedtypes import Seeds


def main():
    n, j, trials, seed, R = [int(x) for x in sys.argv[1:6]]
    rng = random.Random(seed)
    for tr in range(trials):
        PA, PB = random_q(n, rng)
        S = Seeds(PA, PB, j)
        G, m = S.G, S.m
        fibre_of = {}
        for v in range(G.V):
            fibre_of.setdefault(m[v], []).append(v)
        kergroups = [vs for vs in fibre_of.values() if len(vs) > 1]

        def cl(P):
            return closure(G, [S.seed(t, y) for (t, y) in P])

        def score(cls):
            return sum(len({cls[v] for v in vs}) - 1 for vs in kergroups)

        law = None
        for k in range(1, n + 1):
            for Y in itertools.combinations(range(n), k):
                if score(cl([(0, y) for y in Y])) == 0:
                    law = k
                    break
            if law:
                break
        allseeds = [(t, y) for t in range(S.ntypes()) for y in range(n)]
        best, bestP = None, None
        for _ in range(R):
            P = []
            cur = score(cl(P))
            while cur > 0:
                cand = rng.sample(allseeds, min(len(allseeds), 60))
                sc = [(score(cl(P + [s])), rng.random(), s) for s in cand]
                sc.sort()
                P.append(sc[0][2])
                cur = sc[0][0]
            for s in list(P):
                P2 = [x for x in P if x != s]
                if score(cl(P2)) == 0:
                    P = P2
            if best is None or len(P) < best:
                best, bestP = len(P), P
        nover = sum(1 for (t, _) in bestP if t > 0)
        print('trial', tr, 'n', n, 'j', j, 'law', law, 'deep<=', best,
              'overfold in best', nover,
              'FLAG deep<law' if best < law else '')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
