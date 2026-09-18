#!/usr/bin/env python3
"""Check the symbolic heights-uniform bounds of engine_r against exact block sums.

For concrete decorations (D_a, D_b, c) the independent C program pairx.c enumerates
all one-block data pairs and prints exact pair counts N(h, h', k).  From these we form
the exact class matrix  E[s][j] = sup_{h in class s} sum_{h' in class j} sum_k N p^k
(classes -c, 0, c, generic; last column: all h' != 0) and the exact first moment w^2.
The symbolic bound T of engine_r must dominate E entrywise, and the symbolic w must be
<= the exact one.  Prints the largest ratio E/T (must be <= 1).

usage: python3 blockcheck_r.py R          (R = comma list of runs)
"""
import sys, subprocess, os, pickle
from fractions import Fraction as F
import anal, lump
from engine_r import pair_terms, first_moment_terms, matrix, wblock

R = sys.argv[1]
Rt = tuple(int(a) for a in R.split(','))
import engine_r
engine_r.NZREF = os.environ.get('NZREF') == '1'
engine_r.RIGID = os.environ.get('RIGID') == '1'
engine_r.RIGID2 = os.environ.get('RIGID2') == '1'
fn = 'terms_J1_K1_R%s_P0%s.pkl' % ('_'.join(map(str, Rt)),
                                   ('_Z1' if engine_r.NZREF else '') + ('_RG' if engine_r.RIGID else '') + ('2' if engine_r.RIGID2 else ''))
try:
    TE, ncl, FM = pickle.load(open(fn, 'rb'))
except Exception:
    TE, ncl = pair_terms(1, 1, Rt); FM = first_moment_terms(1, Rt)
    pickle.dump((TE, ncl, FM), open(fn, 'wb'))
DECOS = [
    ('S_rig', [0, 1, 3], [0, 1, 4], 1),
    ('S_rig c=2', [0, 1, 3], [0, 1, 4], 2),
    ('S_rig c=3', [0, 1, 3], [0, 1, 4], 3),
    ('AP4 c=1', [0, 1, 2, 3], [0, 1, 2, 3], 1),
    ('AP4 c=2', [0, 1, 2, 3], [0, 1, 2, 3], 2),
    ('AP4 dil c=1', [0, 1, 2, 3], [0, 2, 4, 6], 1),
    ('nr5 c=1', [0, 1, 2, 3, 5], [0, 1, 2, 4, 5], 1),
    ('nr5 c=2', [0, 1, 2, 3, 5], [0, 1, 2, 4, 5], 2),
    ('nr5 c=9', [0, 1, 2, 3, 5], [0, 1, 2, 4, 5], 9),
    ('sidon4 c=1', [0, 1, 4, 9], [0, 2, 7, 11], 1),
    ('rand5 c=3', [0, 2, 3, 7, 8], [1, 2, 6, 9, 10], 3),
    ('AP6 c=1', list(range(6)), list(range(6)), 1),
    ('nr6 c=1', [0, 1, 2, 3, 4, 6], [0, 1, 2, 3, 5, 6], 1),
    ('nr6 c=4', [0, 1, 2, 3, 4, 6], [0, 1, 2, 3, 5, 6], 4),
    ('nr7 c=1', [0, 1, 2, 3, 4, 5, 7], [0, 1, 2, 3, 4, 6, 7], 1),
    ('nr7 c=2', [0, 1, 2, 3, 4, 5, 7], [0, 1, 2, 3, 4, 6, 7], 2),
    ('nr7 c=20', [0, 1, 2, 3, 4, 5, 7], [0, 1, 2, 3, 4, 6, 7], 20),
    ('nr2_6 c=1', [0, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 7], 1),
    ('tri5 c=1', [0, 1, 2, 3, 5], [0, 1, 3, 4, 5], 1),
    ('tri5 c=2', [0, 1, 2, 3, 5], [0, 1, 3, 4, 5], 2),
    ('dil5 c=1', [0, 1, 2, 3, 5], [0, 2, 4, 6, 10], 1),
    ('dil5 c=2', [0, 1, 2, 3, 5], [0, 2, 4, 6, 10], 2),
    ('rand6 c=1', [0, 1, 3, 4, 5, 8], [0, 2, 3, 4, 7, 8], 1),
    ('rand6 c=3', [0, 1, 3, 4, 5, 8], [0, 2, 3, 4, 7, 8], 3),
]


def norm(X):
    a = min(X)
    return tuple(sorted(x - a for x in X))


def rigid(A, B):
    sets = [norm(A), norm([-x for x in A]), norm(B), norm([-x for x in B])]
    return len(set(sets)) == 4


if engine_r.RIGID:
    DECOS = [d for d in DECOS if rigid(d[1], d[2])]
worst = 0.0
for name, A, B, c in DECOS:
    m = len(A)
    out = 'bc_tmp.txt'
    with open(out, 'w') as f:
        subprocess.run(['./pairx', str(c), R, str(m)] + list(map(str, A)) + [str(m)] + list(map(str, B)), stdout=f, check=True)
    ctx = anal.load(out)
    for p in [F(7, 100), F(28, 100) / m]:
        E, w2 = lump.lumped_T(ctx, float(p), c)
        T = matrix(TE, ncl, m, p)
        wb = float(wblock(FM, m, p))
        r = max(E[s][j] / float(T[s][j]) if T[s][j] else (float('inf') if E[s][j] > 1e-15 else 0.0)
                for s in range(4) for j in range(5))
        worst = max(worst, r)
        print('%-12s m=%d p=%.4f  max E/T = %.4f   w_bound/w_exact = %.6f' % (name, m, float(p), r, wb / w2 ** 0.5), flush=True)
    os.remove(out)
print('largest ratio exact/bound: %.4f  %s' % (worst, 'OK' if worst <= 1 else 'VIOLATION'))
