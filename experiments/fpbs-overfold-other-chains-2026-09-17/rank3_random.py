"""Rank-3 target on random (expander-like) transitive Q: deep upper bound versus
law lower bound.

B = <a^2, b, a b a^-1>, A = <b, a^4, a b^2 a^-1> as in rank3_family.py.
- law >= h(Q) = dim_F2 coker(H_1 Gamma_A(Q) -> H_1 Gamma_B(Q))   (rigorous);
- deep <= g(Q) = size of a greedy seed set (over all same-fibre seeds) whose
  fold closure contains ker m                                      (rigorous).
Usage: python3 rank3_random.py n trials seed
"""
import random
import sys
import rank3_family as R
from chains import pair_graphs, transitive
from foldlib import closure, contains_kernel


def greedy_deep(PA, PB):
    GB, GA, m = pair_graphs(PA, PB, R.A, R.B)
    byp = {}
    for v in range(GA.V):
        byp.setdefault(GA.over[v], []).append(v)
    seeds = [(vs[i], vs[k]) for vs in byp.values()
             for i in range(len(vs)) for k in range(i + 1, len(vs))]
    chosen = []
    cls = closure(GA, [])
    while not contains_kernel(GA, cls, m):
        best, bestn = None, -1
        for s in seeds:
            c = closure(GA, chosen + [s])
            nc = len(set(c))
            if best is None or nc < bestn:
                best, bestn = s, nc
        chosen.append(best)
        cls = closure(GA, chosen)
    return len(chosen)


def main():
    n, trials, seed = [int(x) for x in sys.argv[1:4]]
    rng = random.Random(seed)
    done = 0
    while done < trials:
        PA = list(range(n)); rng.shuffle(PA)
        PB = list(range(n)); rng.shuffle(PB)
        if not transitive(PA, PB):
            continue
        done += 1
        print('n', n, 'deep<=', greedy_deep(PA, PB), 'law>=', R.coker_dim(PA, PB),
              flush=True)


if __name__ == '__main__':
    main()
