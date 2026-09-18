#!/usr/bin/env python3
"""Pointwise check of the PW generic row (engine_h, chain deficiency KAP) against exact
block sums of concrete rigid decorations (independent C enumerator pairx.c).
For every letter context (t_i, t) and every generic start offset h (h not in {-c,0,c}),
the exact masses E_j(h) = sum_{h' in class j} sum_k N(h,h',k) p^k must satisfy
E_j(h) <= C_G[j] + sum_k lin_k[j] R_k(h)  for j = -c, 0, c, G, and NZ (all h' != 0),
with R_k(h) = R_kappa(h + j c) evaluated on the actual letter sets.
usage: python3 pwcheck.py m KAP [max #decorations]   (needs ./pairx: gcc -O2 -o pairx ../tree-projected-pollard-slot-second-moment-2026-09-18/pairx.c)"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', 'tree-projected-pollard-slot-second-moment-2026-09-18'))
import sys, subprocess, os, pickle, random
from fractions import Fraction as F
import engine_h as E
E.NZREF = E.RIGID = E.POL = E.NONAP = True; E.PW = True
import runpw
runpw.E = E
import anal
from blockcheck_p import rigid, decos

m = int(sys.argv[1]); E.KAP = int(sys.argv[2]); K = 1
E.M_REF = m; E._cb_memo.clear()
E.PNX = os.environ.get('PNX', '1') == '1'
fn = 'termsH_m%d_k%d_x%d.pkl' % (m, E.KAP, E.PNX)
try:
    TE, ncl = pickle.load(open(fn, 'rb'))
except Exception:
    TE, ncl = E.pair_terms(1, K, (-1, 0, 1)); pickle.dump((TE, ncl), open(fn, 'wb'))

def maxr(D):
    S = set(D)
    return max(sum(1 for x in D if x + g in S) for g in range(1, max(D) - min(D) + 1))

def Rval(key, sets, h, c):
    (kap, j) = key
    (d1, s1), (d2, s2) = kap
    g = h + j * c
    return sum(1 for u in sets[d1] for w in sets[d2] if s1 * u + s2 * w == g)

rng = random.Random(77 + m)
cands = decos(m)
for i in range(6):
    while True:
        A = sorted(rng.sample(range(3 * m), m)); B = sorted(rng.sample(range(3 * m), m))
        if rigid(A, B):
            break
    cands.append(('wide%d c=%d' % (i, i + 1), A, B, [1, 2, 3, 4, 7, 11][i]))
NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 99
cands = [d for d in cands if max(maxr(d[1]), maxr(d[2])) <= m - E.KAP]
# decorations sampled directly under the hypothesis chi >= KAP (max r_D <= m - KAP)
for i in range(4):
    while True:
        Wd = [3 * m, 4 * m, m * m, 2 * m * m][i]
        A = sorted(rng.sample(range(Wd), m)); B = sorted(rng.sample(range(Wd), m))
        if rigid(A, B) and max(maxr(A), maxr(B)) <= m - E.KAP:
            break
    cands.append(('chain%d' % i, A, B, [1, 2, 5, 13][i]))
cands = cands[:NMAX] if len(cands) <= NMAX else cands[:NMAX - 2] + cands[-2:]
worst = 0.0
for name, A, B, c in cands:
    if max(maxr(A), maxr(B)) > m - E.KAP:
        continue
    out = 'pwc_tmp_%d_%d.txt' % (m, E.KAP)
    with open(out, 'w') as f:
        subprocess.run(['./pairx', str(c), '-1,0,1', str(m)] + list(map(str, A)) + [str(m)] + list(map(str, B)),
                       stdout=f, check=True)
    ctx = anal.load(out); os.remove(out)
    Dl = {0: A, 1: [-x for x in A], 2: B, 3: [-x for x in B]}
    for p in [F(7, 100), F(28, 100) / m]:
        C, lin, caps = runpw.matrix_pw(TE, ncl, m, p)
        pf = float(p)
        cls = lambda h: {-c: 0, 0: 1, c: 2}.get(h, 3)
        rmax = 0.0
        for (ti, t), Cx in ctx.items():
            oth = sorted(l for l in range(4) if l not in (ti ^ 1, t))
            sets = {'t': Dl[t], 'o1': Dl[oth[0]], 'o2': Dl[oth[1]]}
            gval = {D: sum(v * pf ** k for k, v in d.items()) for D, d in Cx['g'].items()}
            for h in range(-Cx['H'] - Cx['DW'] - 2, Cx['H'] + Cx['DW'] + 3):
                if h in (-c, 0, c):
                    continue
                if abs(h) <= Cx['H']:
                    masses = {hp: sum(v * pf ** k for k, v in d.items()) for hp, d in Cx['n'][h].items()}
                else:
                    masses = {h + D: v for D, v in gval.items()}
                r = [0.0] * 5
                for hp, v in masses.items():
                    r[cls(hp)] += v
                    if hp != 0:
                        r[4] += v
                bnd = [float(C[ncl - 1][j]) for j in range(5)]
                for k, co in lin.items():
                    Rv = Rval(k, sets, h, c)
                    assert Rv <= caps[k], (k, Rv, caps[k])
                    for j in range(5):
                        bnd[j] += float(co[j]) * Rv
                for j in range(5):
                    if r[j] > 1e-15:
                        rmax = max(rmax, r[j] / bnd[j] if bnd[j] > 0 else float('inf'))
        worst = max(worst, rmax)
        print('%-12s m=%d KAP=%d maxr=%d/%d c=%d p=%.4f  max exact/PW-bound = %.4f' %
              (name, m, E.KAP, maxr(A), maxr(B), c, pf, rmax), flush=True)
print('largest ratio %.4f %s' % (worst, 'OK' if worst <= 1 else 'VIOLATION'))
