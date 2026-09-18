#!/usr/bin/env python3
"""Float scan with the pointwise-in-h generic row (engine_p.PW): the generic source row is
affine in the parameter vector R = (R_kappa(h + j c)) ranging over a box, and
Phi_G(y) = sup over the box of the LP value (itself an LP).
usage: python3 runpw.py m1,m2,...      (J = 1, K = 1, R = -1,0,1; NZREF, RIGID, POL, NONAP on)"""
import sys, os, time, pickle
import numpy as np
from scipy.optimize import linprog
import engine_p as E
from fractions import Fraction as F
from math import sqrt
J, R = 1, (-1, 0, 1)
K = int(os.environ.get('K', '1'))
E.NZREF = E.RIGID = E.POL = E.NONAP = True
E.PW = os.environ.get('PW', '1') == '1'
zero = K


def pstar(m, v=2):
    d = 4 * m + v; la = v + 2 * sqrt(3) * m
    return 2 / (la + sqrt(la * la - 4 * (d - 1)))


def terms(m):
    E.M_REF = m
    E._cb_memo.clear()
    fn = 'termsW_K%d_m%d%s.pkl' % (K, m, '_PW' if E.PW else '')
    try:
        return pickle.load(open(fn, 'rb'))
    except Exception:
        TE, ncl = E.pair_terms(J, K, R)
        pickle.dump((TE, ncl), open(fn, 'wb'))
        return TE, ncl


def matrix_pw(TE, ncl, m, p):
    """const[s][t] and lin[key][t] (generic row only); caps[key]."""
    x = 1 / p
    C = [[F(0)] * (ncl + 1) for _ in range(ncl)]
    lin, caps = {}, {}
    for t in TE:
        st, tg, mult, ne, nq, d = t[:6]
        par = t[6] if len(t) > 6 else None
        v = mult * p ** ne * (x - 1) ** nq * E.desc_value(d, m)
        if par is None:
            C[st][tg] += v
        else:
            assert st == ncl - 1
            lin.setdefault(par, [F(0)] * (ncl + 1))[tg] += v
            caps[par] = E.param_cap(par, m, K)
    return C, lin, caps


def phi_row_lp(Crow, lin, caps, y, zero, ncl):
    """sup over R in box, masses of  Crow0(R) y0 + sum_j mass_j y_j."""
    keys = sorted(lin)
    others = [j for j in range(ncl) if j != zero]
    nR, nM = len(keys), len(others)
    c = np.zeros(nR + nM)
    for i, k in enumerate(keys):
        c[i] = -float(lin[k][zero]) * y[zero]
    for a, j in enumerate(others):
        c[nR + a] = -y[j]
    A, b = [], []
    for a, j in enumerate(others):
        row = np.zeros(nR + nM)
        row[nR + a] = 1
        for i, k in enumerate(keys):
            row[i] = -float(lin[k][j])
        A.append(row); b.append(float(Crow[j]))
    row = np.zeros(nR + nM); row[nR:] = 1
    for i, k in enumerate(keys):
        row[i] = -float(lin[k][ncl])
    A.append(row); b.append(float(Crow[ncl]))
    bounds = [(0, caps[k]) for k in keys] + [(0, None)] * nM
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=bounds, method='highs')
    assert res.status == 0, res.message
    return -res.fun + float(Crow[zero]) * y[zero], res


def phi_pw(Cf, lin, caps, y, zero):
    ncl = len(Cf)
    out = E.phi(Cf, y, zero)
    if lin:
        out[ncl - 1] = phi_row_lp(Cf[ncl - 1], lin, caps, y, zero, ncl)[0]
    return out


def rho_pw(C, lin, caps, L, zero, it=200):
    Cf = [[float(a / L) for a in r] for r in C]
    linf = {k: [float(a / L) for a in v] for k, v in lin.items()}
    ncl = len(C)
    y = [1.0] * ncl
    for _ in range(it):
        z = phi_pw(Cf, linf, caps, y, zero)
        mx = max(z)
        y = [a / mx for a in z]
    z = phi_pw(Cf, linf, caps, y, zero)
    return max(z[i] / y[i] for i in range(ncl)), y


if __name__ == '__main__':
    FM = E.first_moment_terms(J, R)
    for m in [int(a) for a in sys.argv[1].split(',')]:
        t0 = time.time()
        TE, ncl = terms(m)
        lo, hi = 0.2, 0.6
        for _ in range(16):
            mid = (lo + hi) / 2
            p = F(mid).limit_denominator(10 ** 7) / m
            C, lin, caps = matrix_pw(TE, ncl, m, p)
            w = E.wblock(FM, m, p); L = 3 * w * w
            lam, _ = rho_pw(C, lin, caps, L, zero, 80)
            if lam < 1: hi = mid
            else: lo = mid
        ps = F(pstar(m)).limit_denominator(10 ** 9)
        C, lin, caps = matrix_pw(TE, ncl, m, ps); w = E.wblock(FM, m, ps); L = 3 * w * w
        lam, y = rho_pw(C, lin, caps, L, zero, 200)
        print(m, 'terms', len(TE), 'params', len(lin), 'm*p_crit', round(hi, 5), 'm*p*', round(m * float(ps), 5),
              'rho(p*)', round(lam, 5), 'PASS' if hi < m * float(ps) else 'fail', 'time', round(time.time() - t0, 1), flush=True)
        for r in C:
            print('    ', [round(float(a / L), 5) for a in r])
        for k in sorted(lin):
            print('   R', k, 'cap', caps[k], [round(float(a / L), 5) for a in lin[k]])
