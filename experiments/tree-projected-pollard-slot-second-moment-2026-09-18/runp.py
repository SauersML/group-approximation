#!/usr/bin/env python3
"""Float scan: rho(Phi)/(3 w^2) at p*(m,2) and the critical m p of the heights-uniform LP map,
with the Pollard pair refinement (engine_p.POL) on top of NZREF / RIGID (env flags).
usage: python3 runp.py J K R m1,m2,...     (terms are m-specific: rebuilt per m)"""
import sys, os, time, pickle
import engine_p
from engine_p import *
from math import sqrt
J = int(sys.argv[1]); K = int(sys.argv[2]); R = tuple(int(a) for a in sys.argv[3].split(','))
engine_p.NZREF = os.environ.get('NZREF') == '1'
engine_p.RIGID = os.environ.get('RIGID') == '1'
engine_p.POL = os.environ.get('POL', '1') == '1'
engine_p.NONAP = os.environ.get('NONAP') == '1'
ms = [int(a) for a in sys.argv[4].split(',')]
zero = K
def pstar(m, v=2):
    d = 4 * m + v; la = v + 2 * sqrt(3) * m
    return 2 / (la + sqrt(la * la - 4 * (d - 1)))
FM = first_moment_terms(J, R)
for m in ms:
    t0 = time.time()
    engine_p.M_REF = m
    engine_p._cb_memo.clear()
    fn = 'termsP_J%d_K%d_R%s_m%d%s.pkl' % (J, K, '_'.join(map(str, R)), m,
         ('_Z1' if engine_p.NZREF else '') + ('_RG' if engine_p.RIGID else '') + ('_PL' if engine_p.POL else '') + ('_NA' if engine_p.NONAP else ''))
    try:
        TE, ncl = pickle.load(open(fn, 'rb'))
    except Exception:
        TE, ncl = pair_terms(J, K, R)
        pickle.dump((TE, ncl), open(fn, 'wb'))
    lo, hi = 0.2, 0.6
    for _ in range(20):
        mid = (lo + hi) / 2
        p = F(mid).limit_denominator(10 ** 7) / m
        T = matrix(TE, ncl, m, p)
        w = wblock(FM, m, p); L = 3 * w * w
        lam, _ = rho_phi([[a / L for a in r] for r in T], zero, 150)
        if lam < 1: hi = mid
        else: lo = mid
    ps = F(pstar(m)).limit_denominator(10 ** 9)
    T = matrix(TE, ncl, m, ps); w = wblock(FM, m, ps); L = 3 * w * w
    lam, y = rho_phi([[a / L for a in r] for r in T], zero, 300)
    print(m, 'terms', len(TE), 'm*p_crit', round(hi, 5), 'm*p*', round(m * float(ps), 5), 'rho(p*)', round(lam, 5),
          'PASS' if hi < m * float(ps) else 'fail', 'time', round(time.time() - t0, 1), flush=True)
    for r in T:
        print('    ', [round(float(a / L), 5) for a in r])
