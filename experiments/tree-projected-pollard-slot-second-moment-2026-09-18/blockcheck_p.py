#!/usr/bin/env python3
"""Check the m-specific symbolic bounds of engine_p (NZREF + RIGID + POL + NONAP) against
exact block sums of concrete rigid decorations (independent C enumerator pairx.c).

E[s][j] = sup_{h in class s} sum_{h' in class j} sum_k N(h, h', k) p^k  (classes -c, 0, c, G;
last column: all h' != 0) must be dominated entrywise by the symbolic bound T, and the
symbolic one-block weight must be <= the exact one.  Prints the largest ratio E/T.

usage: python3 blockcheck_p.py m1,m2,...
"""
import sys, subprocess, os, pickle, random
from fractions import Fraction as F
import engine_p
engine_p.NZREF = engine_p.RIGID = engine_p.POL = engine_p.NONAP = True
engine_p.PW = False
import anal, lump
from engine_p import pair_terms, first_moment_terms, matrix, wblock


def norm(X):
    a = min(X)
    return tuple(sorted(x - a for x in X))


def rigid(A, B):
    return len({norm(A), norm([-x for x in A]), norm(B), norm([-x for x in B])}) == 4


def decos(m):
    rng = random.Random(1000 + m)
    out = []
    A = list(range(m - 1)) + [m]
    B = list(range(m - 2)) + [m - 1, m]
    for c in (1, 2, 5):
        out.append(('nearAP c=%d' % c, A, B, c))
    A2 = [0, 2] + list(range(3, m + 1))[: m - 2]
    B2 = list(range(m - 3)) + [m - 2, m, m + 1]
    out.append(('nearAP2 c=1', A2, B2, 1))
    for i in range(3):
        while True:
            A = sorted(rng.sample(range(2 * m), m))
            B = sorted(rng.sample(range(2 * m), m))
            if rigid(A, B):
                break
        out.append(('rand%d c=%d' % (i, i + 1), A, B, i + 1))
    return [d for d in out if len(set(d[1])) == m and len(set(d[2])) == m and rigid(d[1], d[2])]


if __name__ == '__main__':
    ms = [int(a) for a in sys.argv[1].split(',')]
    FM = first_moment_terms(1, (-1, 0, 1))
    worst = 0.0
    for m in ms:
        engine_p.M_REF = m
        engine_p._cb_memo.clear()
        fn = 'termsP_J1_K1_R-1_0_1_m%d_Z1_RG_PL_NA.pkl' % m
        try:
            TE, ncl = pickle.load(open(fn, 'rb'))
        except Exception:
            TE, ncl = pair_terms(1, 1, (-1, 0, 1))
            pickle.dump((TE, ncl), open(fn, 'wb'))
        for name, A, B, c in decos(m):
            out = 'bcp_tmp.txt'
            with open(out, 'w') as f:
                subprocess.run(['./pairx', str(c), '-1,0,1', str(m)] + list(map(str, A)) + [str(m)] + list(map(str, B)),
                               stdout=f, check=True)
            ctx = anal.load(out)
            for p in [F(7, 100), F(28, 100) / m]:
                E, w2 = lump.lumped_T(ctx, float(p), c)
                T = matrix(TE, ncl, m, p)
                wb = float(wblock(FM, m, p))
                r = max(E[s][j] / float(T[s][j]) if T[s][j] else (float('inf') if E[s][j] > 1e-15 else 0.0)
                        for s in range(4) for j in range(5))
                worst = max(worst, r)
                print('%-12s m=%2d A=%s B=%s p=%.4f  max E/T = %.4f   w_bound/w_exact = %.6f'
                      % (name, m, A, B, float(p), r, wb / w2 ** 0.5), flush=True)
            os.remove(out)
    print('largest ratio exact/bound: %.4f  %s' % (worst, 'OK' if worst <= 1 else 'VIOLATION'))
