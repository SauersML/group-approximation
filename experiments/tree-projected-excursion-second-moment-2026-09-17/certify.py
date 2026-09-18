#!/usr/bin/env python3
"""Exact certification of the excursion second-moment criterion in rank two.

Part A (tail).  At p = c0/m every entry of T and L = b w^2 is a Laurent polynomial in m
with rational coefficients.  For f in {L-alpha, L-delta, (L-alpha)(L-delta)-beta*gamma}
with top coefficient a_K > 0, f(m) > 0 for every m >= M as soon as
    a_K - sum_{k<K} |a_k| M^(k-K) > 0.
So the criterion holds at p = c0/m for all m >= M_tail.

Part B (range).  For 3 <= m < M_tail and v in VLIST, a rational p <= p*(m,v) is computed
from a rational upper bound of sqrt(3) and an integer square root, and the criterion is
checked exactly at p.

Part C (tail versus p*).  p* >= 1/lam = 1/(v + 2 sqrt(3) m), so c0/m < p* as soon as
m (1 - 2 sqrt(3) c0) > v c0.
"""
from fractions import Fraction as F
from math import isqrt
import sys
from criterion import terms, criterion

N_RANK = 2
B = 2 * N_RANK - 1
E = 2 * N_RANK - 1
S3_UP = F(17321, 10000)   # > sqrt(3):  17321^2 = 300017041 > 3 * 10^8
assert S3_UP ** 2 > 3


def padd(a, b):
    r = dict(a)
    for k, c in b.items():
        r[k] = r.get(k, 0) + c
    return {k: c for k, c in r.items() if c}


def pmul(a, b):
    r = {}
    for k1, c1 in a.items():
        for k2, c2 in b.items():
            r[k1 + k2] = r.get(k1 + k2, 0) + c1 * c2
    return {k: c for k, c in r.items() if c}


def ppow(a, e):
    r = {0: F(1)}
    for _ in range(e):
        r = pmul(r, a)
    return r


def pscale(a, s):
    return {k: c * s for k, c in a.items() if c * s}


def tail(TE, c0):
    P = {-1: c0}                    # p = c0 m^-1
    X1 = {1: 1 / c0, 0: F(-1)}      # x - 1 = m/c0 - 1
    M1 = {1: F(1)}                  # m
    MM1 = {1: F(1), 0: F(-1)}       # m - 1
    T = [[{}, {}], [{}, {}]]
    for (st, tg, mult, ne, nq, d) in TE:
        comps, fedges = d
        term = pscale(pmul(pmul(ppow(P, ne), ppow(X1, nq)), pmul(ppow(M1, comps), ppow(MM1, fedges))), F(mult))
        T[st][tg] = padd(T[st][tg], term)
    w = padd(pmul(M1, P), pmul(pscale(pmul(pmul(ppow(M1, 2), MM1), ppow(P, 3)), F(E - 1)),
                               {0: F(1)}))
    w = padd(w, pmul(pmul(M1, ppow(MM1, 2)), ppow(P, 3)))
    L = pscale(pmul(w, w), F(B))
    al, be, ga, de = T[0][0], T[0][1], T[1][0], T[1][1]
    f1 = padd(L, pscale(al, -1))
    f2 = padd(L, pscale(de, -1))
    f3 = padd(pmul(f1, f2), pscale(pmul(be, ga), -1))
    return f1, f2, f3


def tail_bound(f, M):
    K = max(f)
    aK = f[K]
    return aK - sum(abs(c) * F(M) ** (k - K) for k, c in f.items() if k < K), K, aK


def pstar_low(m, v):
    d = 4 * m + v
    lam = v + 2 * m * S3_UP
    disc = lam * lam - 4 * (d - 1)
    assert disc > 0
    q = 10 ** 8
    sq_up = F(isqrt(int(disc * q * q)) + 1, q)  # >= sqrt(disc)
    return F(2) / (lam + sq_up)


if __name__ == '__main__':
    c0 = F(sys.argv[1]) if len(sys.argv) > 1 else F(7, 25)
    M_tail = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    VLIST = [0, 2]
    TE = terms(E, True)
    print('rank n =', N_RANK, ' symbolic terms:', len(TE))
    print('Part A: tail at p = c0/m, c0 =', c0, '=', float(c0), ' M_tail =', M_tail)
    allok = True
    for name, f in zip(['L-alpha', 'L-delta', '(L-a)(L-d)-bc'], tail(TE, c0)):
        tb, K, aK = tail_bound(f, M_tail)
        print('  %-14s top degree %d, top coeff %.6g, certified margin %.6g -> %s'
              % (name, K, float(aK), float(tb), tb > 0))
        allok &= tb > 0
    # Part C
    gap = 1 - 2 * S3_UP * c0
    print('Part C: 1 - 2 sqrt3 c0 >= %.6g > 0: %s; tail beats p* for m >= v c0 / that = %.4f v'
          % (float(gap), gap > 0, float(c0 / gap) if gap > 0 else float('nan')))
    allok &= gap > 0
    for v in VLIST:
        need = max(M_tail, 0)
        ok_tail = all(m * gap > v * c0 for m in [need])  # linear in m, so m = need suffices
        print('  v = %d: c0/m < 1/lam <= p* for all m >= %d: %s' % (v, need, ok_tail))
        allok &= ok_tail
    print('Part B: exact criterion at rational p <= p*(m,v) for 3 <= m <', M_tail)
    for v in VLIST:
        fails = []
        for m in range(3, M_tail):
            p = pstar_low(m, v)
            p = F(int(p * 10 ** 9), 10 ** 9)
            ok = criterion(TE, N_RANK, m, p)[0]
            if not ok:
                fails.append(m)
        passed = [m for m in range(3, M_tail) if m not in fails]
        M0 = max(fails) + 1 if fails else 3
        print('  v = %d: fails at m in %s; passes for all %d <= m < %d' % (v, fails, M0, M_tail))
    print('ALL TAIL CHECKS PASS' if allok else 'TAIL CHECK FAILED')
