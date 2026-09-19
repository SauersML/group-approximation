#!/usr/bin/env python3
"""Larger Cayley levels, p = 2 only (bit-packed rank): Sanov pair and a random pair
in PSL_2(F_q), q = 13..23, and the Sanov 3-adic level SL_2(Z/27)."""
import random, sys
from census import cayley, ku_p2

rng = random.Random(4242)
sanov = ((1, 2, 0, 1), (1, 0, 2, 1))
def rand_sl2(m):
    while True:
        X = tuple(rng.randrange(m) for _ in range(4))
        if (X[0]*X[3]-X[1]*X[2]) % m == 1:
            return X
for m, proj in ((13, True), (17, True), (19, True), (23, True), (27, False)):
    for name, (ga, gb) in (('sanov', sanov), ('rand', (rand_sl2(m), rand_sl2(m)))):
        A, B = cayley(ga, gb, m, proj)
        n = len(A)
        k = ku_p2(A, B)
        print(f'{"PSL2" if proj else "SL2"}(Z/{m}) {name:5s} |G|={n:6d} k_u(p=2)={k:5d} ratio={k/n:.5f}')
        sys.stdout.flush()
