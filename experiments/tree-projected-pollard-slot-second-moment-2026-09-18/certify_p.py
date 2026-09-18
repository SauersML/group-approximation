#!/usr/bin/env python3
"""Exact certificate for the slot second moment with the rigid collision refinements
(NZREF + RIGID + POL + NONAP of engine_p; J = 1, K = 1, runs R = (-1, 0, 1), v = 2).

usage: python3 certify_p.py m1,m2,...

For each m: p = a rational strictly below p*(m, 2) (the Ihara root); T = exact pair-transfer
bound (engine_p.pair_terms, m-specific because the Pollard / non-AP factors are compared at
M_REF = m); w = exact lower bound for the one-block weight; L = 3 w^2.  Exact rational check
that a positive rational y has Phi(y) < L y componentwise (Collatz-Wielandt for the monotone
homogeneous LP map Phi).  PASS gives p_c <= p < p* <= p_u for every rigid decoration pair
of size m.
"""
import sys, os, pickle
import engine_p
from fractions import Fraction as F
from math import isqrt
engine_p.NZREF = True
engine_p.RIGID = True
engine_p.POL = True
engine_p.NONAP = True
engine_p.PW = False
from engine_p import pair_terms, first_moment_terms, matrix, wblock, phi, rho_phi

J, K, R = 1, 1, (-1, 0, 1)
S3_UP = F(17321, 10000)          # > sqrt(3)


def pstar_low(m, v=2):
    """a rational lower bound for p*(m, v) = 2 / (lam + sqrt(lam^2 - 4 (d - 1)))."""
    d = 4 * m + v
    lam = v + 2 * m * S3_UP
    disc = lam * lam - 4 * (d - 1)
    assert disc > 0
    q = 10 ** 8
    sq_up = F(isqrt(int(disc * q * q)) + 1, q)
    return F(2) / (lam + sq_up)


def terms(m):
    engine_p.M_REF = m
    engine_p._cb_memo.clear()
    fn = 'termsP_J1_K1_R-1_0_1_m%d_Z1_RG_PL_NA.pkl' % m
    try:
        return pickle.load(open(fn, 'rb'))
    except Exception:
        TE, ncl = pair_terms(J, K, R)
        pickle.dump((TE, ncl), open(fn, 'wb'))
        return TE, ncl


if __name__ == '__main__':
    ms = [int(a) for a in sys.argv[1].split(',')]
    FM = first_moment_terms(J, R)
    allok = True
    for m in ms:
        TE, ncl = terms(m)
        ps = pstar_low(m)
        p = F(int(ps * 10 ** 6), 10 ** 6)
        assert p < ps
        T = matrix(TE, ncl, m, p)
        w = wblock(FM, m, p)
        L = 3 * w * w
        lam, y = rho_phi(T, K, 400)
        yq = [F(max(a, 1e-12)).limit_denominator(10 ** 9) for a in y]
        z = phi(T, yq, K)
        ok = all(yq[i] > 0 and z[i] < L * yq[i] for i in range(ncl))
        margin = min(1 - z[i] / (L * yq[i]) for i in range(ncl))
        allok &= ok
        print('m = %2d  terms %d  p = %s (m p = %.6f)  3w = %.6f  rho/L = %.6f  exact margin = %.3e  %s'
              % (m, len(TE), p, float(m * p), float(3 * w), lam / float(L), float(margin),
                 'PASS' if ok else 'fail'), flush=True)
        print('        y =', [str(a) for a in yq], flush=True)
    print('ALL PASS' if allok else 'NOT ALL PASS')
