#!/usr/bin/env python3
"""Float test: h-dependent test function y = (y1, 1, y1) on -c, 0, c and y(h) = a + b S(h) on G,
S = r_{D_a} + r_{D_b} = R_(t,0) + R_(o,0); generic landing mass W(h) pointwise: affine in the
same parameter vector R as the generic row (engine_w.WPW).  usage: python3 runwpw.py m [K]"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', 'tree-projected-pollard-slot-second-moment-2026-09-18'))
import sys, pickle
import numpy as np
from scipy.optimize import linprog, minimize
from fractions import Fraction as F
import engine_w as E
import runpw
E.NZREF = E.RIGID = E.POL = E.NONAP = True
E.PW = True; E.WPW = True
m = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 1
zero = K
runpw.K = K
E.M_REF = m
TE, ncl, WA = pickle.load(open('termsWPW_K%d_m%d.pkl' % (K, m), 'rb'))
FM = E.first_moment_terms(1, (-1, 0, 1))
p = F(runpw.pstar(m)).limit_denominator(10 ** 9)
if len(sys.argv) > 3: p = F(sys.argv[3])
x = 1 / p
w = E.wblock(FM, m, p); L = 3 * w * w
C, lin, caps = runpw.matrix_pw(TE, ncl, m, p)
Cf = [[float(a / L) for a in r] for r in C]
linf = {k: [float(a / L) for a in v] for k, v in lin.items()}
Wc = {}      # (si, kap) -> const
Wl = {}      # kap -> {par: coef}   (generic row only)
for (si, kap, ne, nq, *rest), mult in WA.items():
    d, par = tuple(rest[:-1]), rest[-1]
    v = mult * p ** ne * (x - 1) ** nq * E.desc_value(d, m)
    if par is None:
        Wc[(si, kap)] = Wc.get((si, kap), 0) + v
    else:
        assert si == ncl - 1
        Wl.setdefault(kap, {})
        Wl[kap][par] = Wl[kap].get(par, 0) + v
        caps[par] = E.param_cap(par, m, K)
Wb = [float((Wc.get((s, 't'), 0) + max(Wc.get((s, 'o1'), 0), Wc.get((s, 'o2'), 0))) / L) for s in range(ncl)]
Wlf = {kap: {k: float(v / L) for k, v in d.items()} for kap, d in Wl.items()}
print('W special bounds / L:', [round(a, 4) for a in Wb[:-1]], ' generic const parts t,o1,o2:',
      [round(float(Wc.get((ncl - 1, k), 0) / L), 4) for k in ('t', 'o1', 'o2')])
for kap in Wlf:
    print('  W lin', kap, {str(k): round(v, 4) for k, v in sorted(Wlf[kap].items(), key=lambda z: -z[1])[:8]})
keys = sorted(set(lin) | set().union(*[set(d) for d in Wlf.values()]) if Wlf else set(lin), key=str)
kt = ((('t', -1), ('t', 1)), 0)
kos = [((('o1', -1), ('o1', 1)), 0), ((('o2', -1), ('o2', 1)), 0)]


def lpG(y, b, lam, o):
    others = [j for j in range(ncl) if j != zero]
    nR, nM = len(keys), len(others)
    c = np.zeros(nR + nM)
    ko = kos[o]
    for i, k in enumerate(keys):
        coef = (linf[k][zero] * y[zero] if k in linf else 0.0)
        coef += b * (Wlf.get('t', {}).get(k, 0.0) + Wlf.get('o%d' % (o + 1), {}).get(k, 0.0))
        if k == kt or k == ko:
            coef -= lam * b
        c[i] = -coef
    for a_, j in enumerate(others):
        c[nR + a_] = -y[j]
    A, bb = [], []
    for a_, j in enumerate(others):
        row = np.zeros(nR + nM); row[nR + a_] = 1
        for i, k in enumerate(keys):
            row[i] = -(linf[k][j] if k in linf else 0.0)
        A.append(row); bb.append(Cf[ncl - 1][j])
    row = np.zeros(nR + nM); row[nR:] = 1
    for i, k in enumerate(keys):
        row[i] = -(linf[k][ncl] if k in linf else 0.0)
    A.append(row); bb.append(Cf[ncl - 1][ncl])
    bounds = [(0, caps[k]) for k in keys] + [(0, None)] * nM
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(bb), bounds=bounds, method='highs')
    assert res.status == 0
    Wconst = float((Wc.get((ncl - 1, 't'), 0) + Wc.get((ncl - 1, 'o%d' % (o + 1)), 0)) / L)
    return -res.fun + Cf[ncl - 1][zero] * y[zero] + b * Wconst, res


def excess(v, lam):
    y1, a, b = v
    if min(y1, a, b) < 0:
        return 1e3
    y = [y1] * K + [1.0] + [y1] * K + [a]
    z = E.phi(Cf, y, zero)
    ex = [z[s] + b * Wb[s] - lam * y[s] for s in range(ncl - 1)]
    g = max(lpG(y, b, lam, o)[0] for o in range(2)) - lam * a
    ex.append(g)
    return max(e / max(yy, 1e-9) for e, yy in zip(ex, y))


def best(lam, v0):
    r = minimize(lambda v: excess(v, lam), v0, method='Nelder-Mead',
                 options={'xatol': 1e-8, 'fatol': 1e-10, 'maxiter': 4000})
    return r.fun, r.x


if __name__ == '__main__':
    lo, hi = 0.95, 1.03
    v = np.array([0.165, 0.11, 0.0])
    for _ in range(18):
        mid = (lo + hi) / 2
        f, vv = best(mid, v)
        if f > 0:
            f2, vv2 = best(mid, np.array([v[0], v[1] * 0.5, 0.005]))
            if f2 < f: f, vv = f2, vv2
        if f <= 0:
            hi = mid; v = vv
        else:
            lo = mid
    print('m', m, 'K', K, 'p', float(p), 'augmented lam', round(hi, 5), 'params (y1, a, b)', [round(t, 6) for t in v])
    f0, v0 = best(hi, np.array([v[0], v[1]]) if False else v)
    fb = minimize(lambda u: excess([u[0], u[1], 0.0], hi), v[:2], method='Nelder-Mead').fun
    print('b = 0 excess at that lam:', fb)
