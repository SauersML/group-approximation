#!/usr/bin/env python3
"""Test, on genuine Bernoulli configurations over Z, the ordered termwise split

    I(x_0 ; y_F)  <=  sum_{f in F, 0 in f+E} I(x_0 ; y_f | x_{P_f}),   P_f = (f+E) cap (-inf, 0),

whose right side is at most H(y_0) by the chain rule and translation. Exhaustive over q = 2, k = 1,
random codes psi : {0,1}^E -> {0..r-1}. Prints the worst ratio found.
usage: ordered_split_test.py 'E' 'F' trials r"""
import itertools, math, random, sys
from collections import Counter


def H(counter, total):
    return -sum(c / total * math.log2(c / total) for c in counter.values())


def main():
    E = [int(t) for t in sys.argv[1].split(',')]
    F = [int(t) for t in sys.argv[2].split(',')]
    trials, r = int(sys.argv[3]), int(sys.argv[4])
    sites = sorted(set([0] + [f + e for f in F for e in E]))
    pos = {s: i for i, s in enumerate(sites)}
    rng = random.Random(1)
    worst = -1e9
    for _ in range(trials):
        table = {w: rng.randrange(r) for w in itertools.product((0, 1), repeat=len(E))}
        rows = []
        for x in itertools.product((0, 1), repeat=len(sites)):
            y = tuple(table[tuple(x[pos[f + e]] for e in E)] for f in F)
            rows.append((x, y))
        T = len(rows)
        def ent(fn):
            return H(Counter(fn(x, y) for x, y in rows), T)
        i0 = pos[0]
        lhs = ent(lambda x, y: x[i0]) + ent(lambda x, y: y) - ent(lambda x, y: (x[i0], y))
        rhs = 0.0
        for j, f in enumerate(F):
            if 0 not in [f + e for e in E]:
                continue
            P = [pos[f + e] for e in E if f + e < 0]
            def cond(a, b, P=P):
                return lambda x, y: (tuple(x[p] for p in P),) + tuple(fn(x, y) for fn in (a, b))
            xa = lambda x, y: x[i0]
            ya = lambda x, y, j=j: y[j]
            none = lambda x, y: ()
            rhs += (ent(cond(xa, none)) + ent(cond(none, ya)) - ent(cond(xa, ya)) - ent(cond(none, none)))
        h0 = ent(lambda x, y: table[tuple(x[pos[e]] for e in E)])
        worst = max(worst, lhs - rhs)
        if lhs - rhs > 1e-9:
            print('VIOLATION lhs=%.4f rhs=%.4f H(y)=%.4f table=%s' % (lhs, rhs, h0, table))
            break
    print('E=%s F=%s worst lhs-rhs=%.6f' % (E, F, worst))


if __name__ == '__main__':
    main()
