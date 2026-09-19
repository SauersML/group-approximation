"""Cross-check: least number of vertex merges rho(Q) on Gamma_K over Q equals
the least 2-of-3 percolating set r(Q) on the triples {y, y.a^-1, y.b^-1}
(right action; this is the triple (y, a y, b y) of the left action
g.y := y.g^-1).  Also checks the structural description of Gamma_K over Q:
three vertices over every point (R_y, W_y, X_y).

Usage: python3 rho_vs_r.py nmax trials seed
"""
import itertools
import random
import sys
from wordchords import build_gamma_k, random_q, rho_exact, tables


def closure(S, n, IA, IB):
    S = set(S)
    changed = True
    while changed:
        changed = False
        for y in range(n):
            tri = (y, IA[y], IB[y])
            inside = sum(1 for t in tri if t in S)
            if inside >= 2:
                for t in tri:
                    if t not in S:
                        S.add(t)
                        changed = True
    return S


def r_exact(n, IA, IB, maxk):
    for k in range(0, maxk + 1):
        for S in itertools.combinations(range(n), k):
            if len(closure(S, n, IA, IB)) == n:
                return k
    return None


def run(nmax, trials, seed):
    rng = random.Random(seed)
    bad = 0
    tot = 0
    for n in range(2, nmax + 1):
        for _ in range(trials):
            PA, PB = random_q(n, rng)
            F, tab = build_gamma_k(PA, PB)
            _, IA, _, IB = tab
            assert F.nroots() == 3 * n
            rho = rho_exact(F, n, 4)
            r = r_exact(n, IA, IB, 4)
            # the other convention, for comparison only
            r_other = r_exact(n, PA, PB, 4)
            tot += 1
            if rho != r:
                bad += 1
                print('MISMATCH n', n, 'PA', PA, 'PB', PB, 'rho', rho, 'r', r)
            print('n', n, 'rho', rho, 'r', r, 'r_other_convention', r_other)
    print('total', tot, 'mismatches', bad)


if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    run(*a)
