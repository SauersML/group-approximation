#!/usr/bin/env python3
"""Exact certificate: slot second moment (J=1, K=1, runs -1,0,1, v=2) with the rigid
refinements NZREF+RIGID+POL+NONAP and the pointwise generic row PW, under the chain
deficiency hypothesis  |D cap (D+g)| <= m-KAP  (all letter sets D, all g != 0).
KAP=2 holds for every rigid decoration.
usage: python3 certify_h.py m KAP
Generic row: Phi_G(y) = sup over R in the box prod [0,cap_k] of an LP in the masses; an
exact upper bound is obtained from a rational dual solution (weak duality), see dual_bound.
PASS: Phi(y) < L y componentwise with y > 0 rational, p < p*(m,2) rational, L = 3 w^2."""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', 'tree-projected-pollard-slot-second-moment-2026-09-18'))
import sys, os, pickle
import numpy as np
from fractions import Fraction as F
import engine_h as E
E.NZREF = E.RIGID = E.POL = E.NONAP = True; E.PW = True
import runpw
runpw.E = E
from certify_p import pstar_low
m = int(sys.argv[1]); E.KAP = int(sys.argv[2]); K = 1
E.M_REF = m; E._cb_memo.clear()
E.PNX = os.environ.get('PNX', '1') == '1'
fn = 'termsH_m%d_k%d_x%d.pkl' % (m, E.KAP, E.PNX)
try:
    TE, ncl = pickle.load(open(fn, 'rb'))
except Exception:
    TE, ncl = E.pair_terms(1, K, (-1, 0, 1)); pickle.dump((TE, ncl), open(fn, 'wb'))
FM = E.first_moment_terms(1, (-1, 0, 1))
ps = pstar_low(m)
p = F(int(ps * 10 ** 6), 10 ** 6); assert p < ps
C, lin, caps = runpw.matrix_pw(TE, ncl, m, p)
w = E.wblock(FM, m, p); L = 3 * w * w
lam, y = runpw.rho_pw(C, lin, caps, L, K, 400)
yq = [F(max(a, 1e-12)).limit_denominator(10 ** 9) for a in y]
G = ncl - 1
others = [j for j in range(ncl) if j != K]
keys = sorted(lin)

def dual_bound(yv, ud, ut):
    """Upper bound for  max sum_k lin_k[K] yK R_k + sum_j M_j y_j  s.t.
    M_j <= C_j + lin_k[j] R_k (j != K), sum_j M_j <= C_tot + lin_k[tot] R_k, M >= 0, 0<=R<=cap.
    Multipliers ud_j, ut >= 0 with ud_j + ut >= y_j give the bound
    sum_j ud_j C_j + ut C_tot + C_K yK + sum_k cap_k max(0, coef_k)."""
    val = sum(ud[j] * C[G][j] for j in others) + ut * C[G][ncl] + C[G][K] * yv[K]
    for k in keys:
        co = lin[k][K] * yv[K] + sum(ud[j] * lin[k][j] for j in others) + ut * lin[k][ncl]
        if co > 0:
            val += caps[k] * co
    return val

# float LP duals
Cf = [[float(a / L) for a in r] for r in C]
linf = {k: [float(a / L) for a in v] for k, v in lin.items()}
_, res = runpw.phi_row_lp(Cf[G], linf, caps, [float(a) for a in yq], K, ncl)
marg = -np.array(res.ineqlin.marginals)       # >= 0 duals of the <= rows
ut = F(max(marg[-1], 0)).limit_denominator(10 ** 12)
ud = {}
for a, j in enumerate(others):
    u = F(max(marg[a], 0)).limit_denominator(10 ** 12)
    ud[j] = max(u, yq[j] - ut, F(0))
z = E.phi(C, yq, K)
z[G] = dual_bound(yq, ud, ut)
ok = all(yq[i] > 0 and z[i] < L * yq[i] for i in range(ncl))
margin = min(1 - z[i] / (L * yq[i]) for i in range(ncl))
neg = sum(1 for k in keys for a in lin[k] if a < 0)
print('m = %d KAP = %d terms %d params %d negcoef %d p = %s (m p = %.6f) rho = %.6f exact margin = %.3e %s'
      % (m, E.KAP, len(TE), len(keys), neg, p, float(m * p), lam, float(margin), 'PASS' if ok else 'fail'), flush=True)
print('  y =', [str(a) for a in yq])
print('  ratios =', [float(z[i] / (L * yq[i])) for i in range(ncl)])
