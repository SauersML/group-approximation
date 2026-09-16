#!/usr/bin/env python3
"""Referee falsification probe for Theorem A of
research/artifacts/leavitt-thompson-unit-centralizer-rank-2026-09-16.md.

For random infinite-order elements g of V (codes of length <= 3, order not detected up to 64), compute the
eventual increment of dim span{u^i z : i <= j, z in C_R(u_g) cap R_N}.  This is a lower bound for rho(u_g).
A value above min(N(g), N(g^-1)) would contradict Theorem A.  Evidence only.

Usage: python3 referee_randtest.py SEED N COUNT   (run: 11 2 12)
"""
import random, sys, time
from thompson_rank import *

rng = random.Random(int(sys.argv[1]))
N = int(sys.argv[2])
cnt = 0
t0 = time.time()
while cnt < int(sys.argv[3]) and time.time() - t0 < 500:
    n = rng.randrange(2, 5)
    g = reduce_rules(random_V(n, rng))
    if Lmax(g) > 3:
        continue
    if order(g) is not None:
        continue
    b1, s1, c1 = rank_bound(g)
    b2, s2, c2 = rank_bound(inverse(g))
    dimRN, ker = centralizer_basis(g, N)
    inc = increments(g, ker, 6)
    cnt += 1
    flag = 'VIOLATION' if inc[-1] > min(b1, b2) else ''
    print(g, 'N(g)=', b1, 'N(g^-1)=', b2, 'dimC=', len(ker), 'inc=', inc, flag, flush=True)
