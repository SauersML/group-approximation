#!/usr/bin/env python3
"""Exact certificate for the vertical-run slot second moment (v = 2).

usage: python3 certify_r.py J K R m_lo m_hi        (R = comma list of runs, e.g. -1,0,1)

Same as certify_v.py of w5-009 (whose engine this extends), with the single optional
up-step replaced by a vertical run r in R per slot (r > 0: r steps z -> z + c,
r < 0: |r| steps z -> z - c, both along generators of the vertical part {(1, +-c)}).
For each m: p = a rational strictly below p*(m, 2); T = exact pair-transfer bound
(engine_r.pair_terms), w = exact lower bound for the one-block weight, L = 3 w^2; exact
check that a positive rational y has Phi(y) < L y componentwise (Collatz-Wielandt for
the monotone homogeneous LP map Phi).  PASS gives p_c <= p < p* <= p_u.
"""
import sys, pickle, os
import engine_r
engine_r.NZREF = os.environ.get('NZREF') == '1'   # refined nonzero capacity (see engine_r)
engine_r.RIGID = os.environ.get('RIGID') == '1'
engine_r.RIGID2 = os.environ.get('RIGID2') == '1'   # rigid-decoration counting (see engine_r)
from fractions import Fraction as F
from math import isqrt
from engine_r import pair_terms, first_moment_terms, matrix, wblock, phi, rho_phi

S3_UP = F(17321, 10000)


def pstar_low(m, v):
    d = 4 * m + v
    lam = v + 2 * m * S3_UP
    disc = lam * lam - 4 * (d - 1)
    assert disc > 0
    q = 10 ** 8
    sq_up = F(isqrt(int(disc * q * q)) + 1, q)  # >= sqrt(disc)
    return F(2) / (lam + sq_up)


def load(J, K, R):
    fn = 'terms_J%d_K%d_R%s_P0%s.pkl' % (J, K, '_'.join(map(str, R)),
                                         ('_Z1' if engine_r.NZREF else '') + ('_RG' if engine_r.RIGID else '') + ('2' if engine_r.RIGID2 else ''))
    try:
        return pickle.load(open(fn, 'rb'))
    except Exception:
        TE, ncl = pair_terms(J, K, R)
        FM = first_moment_terms(J, R)
        pickle.dump((TE, ncl, FM), open(fn, 'wb'))
        return TE, ncl, FM


def check(TE, ncl, FM, m, p, zero):
    T = matrix(TE, ncl, m, p)
    w = wblock(FM, m, p)
    L = 3 * w * w
    lam, y = rho_phi(T, zero, 400)
    yq = [F(max(a, 1e-12)).limit_denominator(10 ** 9) for a in y]
    z = phi(T, yq, zero)
    ok = all(z[i] < L * yq[i] for i in range(ncl))
    margin = min(1 - z[i] / (L * yq[i]) for i in range(ncl))
    return ok, float(lam / float(L)), float(margin), float(w), yq


if __name__ == '__main__':
    J, K = int(sys.argv[1]), int(sys.argv[2])
    R = tuple(int(a) for a in sys.argv[3].split(','))
    mlo, mhi = int(sys.argv[4]), int(sys.argv[5])
    TE, ncl, FM = load(J, K, R)
    print('NZREF', engine_r.NZREF, 'RIGID', engine_r.RIGID)
    print('J =', J, 'K =', K, 'R =', R, 'classes', ncl, 'terms', len(TE), 'first-moment terms', len(FM))
    allok = True
    for m in range(mlo, mhi + 1):
        ps = pstar_low(m, 2)
        p = F(int(ps * 10 ** 6), 10 ** 6)
        assert p < ps
        ok, r, mg, w, yq = check(TE, ncl, FM, m, p, K)
        allok &= ok
        print('m = %2d  p = %s (m p = %.5f)  3w = %.5f  rho_Phi/L = %.5f  exact margin = %.3e  %s'
              % (m, p, float(m * p), 3 * w, r, mg, 'PASS' if ok else 'fail'), flush=True)
        print('        y =', [str(a) for a in yq], flush=True)
    print('ALL PASS' if allok else 'NOT ALL PASS')
