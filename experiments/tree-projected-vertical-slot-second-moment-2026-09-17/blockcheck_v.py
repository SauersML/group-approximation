#!/usr/bin/env python3
"""Brute-force check of the symbolic bounds on concrete decorations.

usage: python3 blockcheck_v.py J K

For random decoration triples (D_t, D_o1, D_o2) of size m, vertical height c, and every
offset h with |h| <= H, enumerate all pairs of block data of the vertical-slot ensemble
exactly (edges = (label, lower height, upper height)), and compare:
  * the exact one-block weight with the lower bound wblock(first_moment_terms);
  * the exact pair sum from h into each offset class, and into all nonzero offsets,
    with the entries of engine.matrix(pair_terms).
"""
import sys, random, pickle
from fractions import Fraction as F
from itertools import product
from engine import pair_terms, first_moment_terms, matrix, wblock


def block_data(J, D, c):
    out = []
    lets = ['t', 'o1', 'o2']
    for V in (0, 1):
        for j in range(J + 1):
            for seq in product(lets, repeat=j):
                def rec(i, z, edges, prev):
                    if i == len(seq):
                        for s in D['t']:
                            if prev is not None and prev[0] == 't' and s == prev[1]:
                                continue
                            E = edges + [('t', z, z + s)]
                            if len(set(E)) < len(E):
                                continue
                            out.append((frozenset(E), len(E), z + s))
                        return
                    e = seq[i]
                    for u in D[e]:
                        if prev is not None and prev[0] == e and u == prev[1]:
                            continue
                        for v in D[e]:
                            if v == u:
                                continue
                            y = z + u
                            rec(i + 1, y - v, edges + [(e, z, y), (e, y - v, y)], (e, v))
                z0 = c if V else 0
                rec(0, z0, [('vert', 0, c)] if V else [], None)
    return out


def shift(E, h):
    return frozenset((l, a + h, b + h) for (l, a, b) in E)


if __name__ == '__main__':
    J, K = int(sys.argv[1]), int(sys.argv[2])
    TE, ncl = pair_terms(J, K, True)
    FM = first_moment_terms(J, True)
    specials = list(range(-K, K + 1))
    random.seed(1)
    worst = 0.0
    for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 4):
        m = random.choice([3, 4])
        p = F(1, 10) if m == 3 else F(7, 100)
        x = 1 / p
        c = random.randint(1, 4)
        D = {k: sorted(random.sample(range(-6, 7), m)) for k in ['t', 'o1', 'o2']}
        FIXED = [({'t': [0, 1, 3], 'o1': [0, 1, 4], 'o2': [-4, -1, 0]}, 1),   # S_rig
                 ({'t': [0, 1, 2], 'o1': [0, 1, 2], 'o2': [0, 1, 2]}, 1),     # APs, c = step
                 ({'t': [0, 1, 2], 'o1': [-2, -1, 0], 'o2': [0, 2, 4]}, 2),
                 ({'t': [0, 1, 3], 'o1': [0, 2, 3], 'o2': [0, 1, 3]}, 1)]
        if trial < len(FIXED):
            D, c = FIXED[trial]; m = 3; p = F(1, 10); x = 1 / p
        BD = block_data(J, D, c)
        w_ex = sum(p ** ne for (_, ne, _) in BD)
        w_lo = wblock(FM, m, p)
        assert w_ex >= w_lo, (w_ex, w_lo)
        T = matrix(TE, ncl, m, p)
        H = 3 * c + 4
        for h in range(-H, H + 1):
            if h in [k * c for k in specials]:
                s = specials.index(h // c)
            else:
                s = ncl - 1
            mass = [F(0)] * ncl
            nz = F(0)
            for (E1, n1, d1) in BD:
                for (E2, n2, d2) in BD:
                    sh = len(E1 & shift(E2, h))
                    wt = p ** (n1 + n2) * x ** sh
                    hp = h + d2 - d1
                    if hp in [k * c for k in specials]:
                        mass[specials.index(hp // c)] += wt
                    else:
                        mass[ncl - 1] += wt
                    if hp != 0:
                        nz += wt
            for tcl in range(ncl):
                assert mass[tcl] <= T[s][tcl], ('FAIL', D, c, h, tcl, float(mass[tcl]), float(T[s][tcl]))
                if T[s][tcl] > 0:
                    worst = max(worst, float(mass[tcl] / T[s][tcl]))
            assert nz <= T[s][ncl], ('FAIL NZ', D, c, h, float(nz), float(T[s][ncl]))
        print('trial', trial, 'm', m, 'c', c, D, 'w exact %.5f >= w_low %.5f' % (w_ex, w_lo),
              'data', len(BD), 'ok', flush=True)
    print('all bounds hold; max ratio exact/bound = %.4f' % worst)
