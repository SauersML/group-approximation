#!/usr/bin/env python3
"""Validate: (1) the 9-term s=0 norm equals the determinant of right multiplication
(random integer pieces); (2) multiplicativity on random 3-coset elements."""
import random, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from engine import *
random.seed(20260916)
def rnd(n=3, box=1, cmax=2):
    return {(random.randint(-box, box), random.randint(-box, box), random.randint(-box, box)): random.randint(-cmax, cmax) or 1 for _ in range(n)}
ok = True
for trial in range(30):
    p, q, r = rnd(), rnd(), rnd()
    u = assemble(p, q, r)
    if det_right_mult(u) != nrd3(p, q, r):
        ok = False
        print('MISMATCH', trial)
print('V1 nine-term s=0 norm == det of right multiplication on 30 random Z-samples:', ok)
ok2 = True
for trial in range(10):
    u = assemble(rnd(), rnd(), rnd(), rnd())
    v = assemble(rnd(), rnd(), rnd(), rnd())
    if det_right_mult(gmul(u, v)) != pmul(det_right_mult(u), det_right_mult(v)):
        ok2 = False
print('V2 det multiplicative on 10 random pairs of 4-coset Z-elements:', ok2)
