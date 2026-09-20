"""Size of the depth-j homological certificate B_j = k_{u_{j+1}} - k_{u_j}
on large random levels, over F_p (p = 2, 3, and the large prime 1000003 as a
proxy for characteristic 0).  u_i = d t_i / d b acting on F_p[Q] on the right.
Usage: python3 scale.py jmax trials seed n1 n2 ...
"""
import os
import sys
import random
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from cert import fox_b, inv_perm, act  # noqa
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..',
                                'fpbs-depth-overfolding-2026-09-17'))
from foldlib import t  # noqa


def rank_p(M, p):
    M = M.copy() % p
    rows, cols = M.shape
    rk = 0
    for c in range(cols):
        nz = np.nonzero(M[rk:, c])[0]
        if len(nz) == 0:
            continue
        piv = rk + nz[0]
        if piv != rk:
            M[[rk, piv]] = M[[piv, rk]]
        iv = pow(int(M[rk, c]), p - 2, p)
        M[rk] = (M[rk] * iv) % p
        col = M[:, c].copy()
        col[rk] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            M[nzr] = (M[nzr] - np.outer(col[nzr], M[rk])) % p
        rk += 1
        if rk == rows:
            break
    return rk


def k_u(terms, PA, PB, p):
    n = len(PA)
    IA, IB = inv_perm(PA), inv_perm(PB)
    M = np.zeros((n, n), dtype=np.int64)
    for q in range(n):
        for s, w in terms:
            M[q, act(q, w, PA, PB, IA, IB)] += s
    return n - rank_p(M, p)


def main():
    jmax, trials, seed = [int(x) for x in sys.argv[1:4]]
    ns = [int(x) for x in sys.argv[4:]]
    rng = random.Random(seed)
    us = [None] + [fox_b(t(i)) for i in range(1, jmax + 2)]
    for n in ns:
        for p in (2, 3, 1000003):
            worst = [0] * (jmax + 1)
            for _ in range(trials):
                PA = list(range(n)); rng.shuffle(PA)
                PB = list(range(n)); rng.shuffle(PB)
                ks = [0] + [k_u(us[i], PA, PB, p) for i in range(1, jmax + 2)]
                for j in range(jmax + 1):
                    worst[j] = max(worst[j], ks[j + 1] - ks[j])
            print('n', n, 'p', p, 'max B_j over', trials, 'levels, j=0..%d:' % jmax,
                  worst, ' max B_j/n:', ['%.4f' % (b / n) for b in worst])
            sys.stdout.flush()


if __name__ == '__main__':
    main()
