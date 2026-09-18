#!/usr/bin/env python3
"""Build the PW terms together with the S-weighted landing terms W_AGG (engine_p.WAUG) and
print W(s, kap) / (3 w^2) at p*(m, 2).
usage: python3 runwa.py m"""
import sys, pickle, time
import engine_p as E
from fractions import Fraction as F
from math import sqrt
E.NZREF = E.RIGID = E.POL = E.NONAP = True
E.PW = True
E.WAUG = True
m = int(sys.argv[1])
K = 1


def pstar(m, v=2):
    d = 4 * m + v; la = v + 2 * sqrt(3) * m
    return 2 / (la + sqrt(la * la - 4 * (d - 1)))


t0 = time.time()
E.M_REF = m
E._cb_memo.clear()
E.W_AGG.clear()
TE, ncl = E.pair_terms(1, K, (-1, 0, 1))
pickle.dump((TE, ncl, dict(E.W_AGG)), open('termsWA_K%d_m%d.pkl' % (K, m), 'wb'))
print('built in', round(time.time() - t0), 's; W terms', len(E.W_AGG), flush=True)
FM = E.first_moment_terms(1, (-1, 0, 1))
p = F(pstar(m)).limit_denominator(10 ** 9)
x = 1 / p
w = E.wblock(FM, m, p); L = 3 * w * w
W = {}
for (si, kap, ne, nq, *d), mult in E.W_AGG.items():
    W[(si, kap)] = W.get((si, kap), 0) + mult * p ** ne * (x - 1) ** nq * E.desc_value(tuple(d), m)
for k in sorted(W, key=str):
    print(k, round(float(W[k] / L), 6))
