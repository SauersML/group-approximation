#!/usr/bin/env python3
"""Float test of the S-augmented Collatz-Wielandt check (heights-uniform).
Test function: y = (y1, 1, y1) on the special classes -c, 0, c and y(h) = a + b S(h) on the
generic class, S(h) = r_{D_a}(h) + r_{D_b}(h) = R_t,0(h) + R_{o*},0(h).
Rows:  special s: Phi_s(y1, 1, y1, a) + b (W_t(s) + max(W_o1(s), W_o2(s))) <= lam y_s;
       generic:  max_{o in o1,o2} sup_R [LP_G(R) - lam b (R_t,0 + R_o,0)] + b W_G <= lam a
(the uniform W_G bound of W_AGG, not pointwise in h).
usage: python3 runwa2.py m"""
import sys, pickle
import numpy as np
from scipy.optimize import linprog, minimize
from fractions import Fraction as F
from math import sqrt
import engine_p as E
import runpw
E.NZREF = E.RIGID = E.POL = E.NONAP = True
E.PW = True
m = int(sys.argv[1]); K = 1; zero = K
runpw.K = K
E.M_REF = m
TE, ncl, WA = pickle.load(open('termsWA_K%d_m%d.pkl' % (K, m), 'rb'))
FM = E.first_moment_terms(1, (-1, 0, 1))
p = F(runpw.pstar(m)).limit_denominator(10 ** 9)
x = 1 / p
w = E.wblock(FM, m, p); L = 3 * w * w
C, lin, caps = runpw.matrix_pw(TE, ncl, m, p)
Cf = [[float(a / L) for a in r] for r in C]
linf = {k: [float(a / L) for a in v] for k, v in lin.items()}
W = {}
for (si, kap, ne, nq, *d), mult in WA.items():
    W[(si, kap)] = W.get((si, kap), 0) + mult * p ** ne * (x - 1) ** nq * E.desc_value(tuple(d), m)
Wb = [float((W.get((s, 't'), 0) + max(W.get((s, 'o1'), 0), W.get((s, 'o2'), 0))) / L) for s in range(ncl)]
print('W bounds / L:', [round(a, 4) for a in Wb])
keys = sorted(lin, key=str)
kt = ((('t', -1), ('t', 1)), 0)
ko = [((('o1', -1), ('o1', 1)), 0), ((('o2', -1), ('o2', 1)), 0)]


def lpG(y, extra):
    """sup over R box and masses of C0(R) y0 + sum_j mass_j y_j + extra . R"""
    others = [j for j in range(ncl) if j != zero]
    nR, nM = len(keys), len(others)
    c = np.zeros(nR + nM)
    for i, k in enumerate(keys):
        c[i] = -(linf[k][zero] * y[zero] + extra.get(k, 0.0))
    for a_, j in enumerate(others):
        c[nR + a_] = -y[j]
    A, bb = [], []
    for a_, j in enumerate(others):
        row = np.zeros(nR + nM); row[nR + a_] = 1
        for i, k in enumerate(keys):
            row[i] = -linf[k][j]
        A.append(row); bb.append(Cf[ncl - 1][j])
    row = np.zeros(nR + nM); row[nR:] = 1
    for i, k in enumerate(keys):
        row[i] = -linf[k][ncl]
    A.append(row); bb.append(Cf[ncl - 1][ncl])
    bounds = [(0, caps[k]) for k in keys] + [(0, None)] * nM
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(bb), bounds=bounds, method='highs')
    assert res.status == 0
    return -res.fun + Cf[ncl - 1][zero] * y[zero]


def excess(v, lam):
    y1, a, b = v
    if min(y1, a, b) < 0:
        return 1e3
    y = [y1, 1.0, y1, a]
    z = E.phi(Cf, y, zero)
    ex = [z[s] + b * Wb[s] - lam * y[s] for s in range(ncl - 1)]
    g = max(lpG(y, {kt: -lam * b, ko[i]: -lam * b}) for i in range(2)) + b * Wb[ncl - 1] - lam * a
    ex.append(g)
    return max(e / max(yy, 1e-9) for e, yy in zip(ex, y))


def best(lam, v0):
    r = minimize(lambda v: excess(v, lam), v0, method='Nelder-Mead',
                 options={'xatol': 1e-7, 'fatol': 1e-9, 'maxiter': 3000})
    return r.fun, r.x


v0 = [0.165, 0.11, 0.0]
f0, _ = best(1.0053, [0.165, 0.11])  if False else (None, None)
lo, hi = 0.97, 1.02
v = np.array(v0)
for _ in range(18):
    mid = (lo + hi) / 2
    f, vv = best(mid, v)
    if f <= 0:
        hi = mid; v = vv
    else:
        lo = mid
print('m', m, 'augmented lam', round(hi, 5), 'params (y1, a, b)', [round(t, 6) for t in v])
fb, vb = minimize(lambda u: excess([u[0], u[1], 0.0], hi), v[:2], method='Nelder-Mead').fun, None
print('constant-test-function check at that lam: excess', fb)
