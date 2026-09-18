#!/usr/bin/env python3
"""Exact certificate for the vertical-slot second moment (v = 2).

usage: python3 certify_v.py J K m_lo m_hi

For each m in [m_lo, m_hi]:
  * p = a rational strictly below p*(m, 2) (sqrt 3 < 17321/10000, integer square root
    rounded up, then truncated to 6 decimals);
  * T = exact pair-transfer bound (engine.pair_terms), w = exact lower bound for the
    one-block weight (engine.first_moment_terms), L = 3 w^2;
  * exact check that some positive rational y has Phi(y) < L y componentwise, where Phi
    is the monotone LP map of engine.phi (Collatz-Wielandt for a monotone homogeneous
    map).  PASS means the Paley-Zygmund criterion holds, hence p_c <= p < p* <= p_u.
"""
import sys, pickle
from fractions import Fraction as F
from math import isqrt
from engine import pair_terms, first_moment_terms, matrix, wblock, phi, rho_phi

S3_UP = F(17321, 10000)


def pstar_low(m, v):
    d = 4 * m + v
    lam = v + 2 * m * S3_UP
    disc = lam * lam - 4 * (d - 1)
    assert disc > 0
    q = 10 ** 8
    sq_up = F(isqrt(int(disc * q * q)) + 1, q)  # >= sqrt(disc)
    return F(2) / (lam + sq_up)


def load(J, K):
    fn = 'terms_J%d_K%d_V1.pkl' % (J, K)
    try:
        return pickle.load(open(fn, 'rb'))
    except Exception:
        TE, ncl = pair_terms(J, K, True)
        FM = first_moment_terms(J, True)
        pickle.dump((TE, ncl, FM), open(fn, 'wb'))
        return TE, ncl, FM


def check(TE, ncl, FM, m, p, zero):
    T = matrix(TE, ncl, m, p)
    w = wblock(FM, m, p)
    L = 3 * w * w
    lam, y = rho_phi(T, zero, 400)
    # rational candidate vector, slightly inflated on the zero class is not needed:
    yq = [F(max(a, 1e-12)).limit_denominator(10 ** 9) for a in y]
    z = phi(T, yq, zero)
    ok = all(z[i] < L * yq[i] for i in range(ncl))
    margin = min(1 - z[i] / (L * yq[i]) for i in range(ncl))
    return ok, float(lam / float(L)), float(margin), float(w)


if __name__ == '__main__':
    J, K, mlo, mhi = map(int, sys.argv[1:5])
    TE, ncl, FM = load(J, K)
    print('J =', J, 'K =', K, 'classes', ncl, 'terms', len(TE), 'first-moment terms', len(FM))
    allok = True
    for m in range(mlo, mhi + 1):
        ps = pstar_low(m, 2)
        p = F(int(ps * 10 ** 6), 10 ** 6)
        assert p < ps
        ok, r, mg, w = check(TE, ncl, FM, m, p, K)
        allok &= ok
        print('m = %2d  p = %s (m p = %.5f)  3w = %.5f  rho_Phi/L = %.5f  exact margin = %.3e  %s'
              % (m, p, float(m * p), 3 * w, r, mg, 'PASS' if ok else 'fail'), flush=True)
    print('ALL PASS' if allok else 'NOT ALL PASS')
