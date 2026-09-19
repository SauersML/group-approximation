"""Greedy upper bounds for law_j(Q) = r(Q^(j)) on random Q, by depth j.

Q^(j) is Q with L acting through phi^j (a -> a, b -> t_j).  law_j(Q), the
least number of lawful seeds, equals the depth-0 seed number r(Q^(j)) (the
lawful depth-j problem is the depth-0 problem of the L_j-action,
transported by phi^j).  Greedy: add the lawful seed that most reduces the
number of unmerged kernel pairs, then prune.  Upper bounds only.
Also prints the L_j-orbit count of Q.
Usage: python3 law_by_depth.py n jmax trials seed
"""
import random
import sys
from foldlib import random_q, depth_graphs, closure, inverse_perm, act, t


def orbits(PA, PB):
    n = len(PA)
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for p in range(n):
        par[f(p)] = f(PA[p])
        par[f(p)] = f(PB[p])
    return len({f(p) for p in range(n)})


def greedy_r(PA, PB, rng):
    Gj, G, m = depth_graphs(PA, PB, 0)
    n = len(PA)
    fib = {}
    for v in range(G.V):
        fib.setdefault(G.over[v], []).append(v)
    seeds = [(fib[y][0], fib[y][1]) for y in range(n)]

    def score(P):
        cls = closure(G, P)
        return sum(len({cls[v] for v in vs}) - 1 for vs in fib.values())
    P = []
    cur = score(P)
    while cur > 0:
        cand = rng.sample(seeds, min(n, 40))
        best = min(cand, key=lambda s: (score(P + [s]), rng.random()))
        P.append(best)
        cur = score(P)
    for s in list(P):
        P2 = [x for x in P if x != s]
        if score(P2) == 0:
            P = P2
    return len(P)


def main():
    n, jmax, trials, seed = [int(x) for x in sys.argv[1:5]]
    rng = random.Random(seed)
    for tr in range(trials):
        PA, PB = random_q(n, rng)
        IA, IB = inverse_perm(PA), inverse_perm(PB)
        row = []
        for j in range(jmax + 1):
            PBj = [act(p, t(j), PA, PB, IA, IB) for p in range(n)]
            r = greedy_r(PA, PBj, rng)
            row.append('j%d: r<=%d (%.3f) orbits %d' % (
                j, r, r / n, orbits(PA, PBj)))
        print('n', n, ' | '.join(row))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
