#!/usr/bin/env python3
"""Checks for the radius-one ball family B_s = {0, e_1..e_(s-1)} in F_2^(s-1), s = 2^j.

(1) Graph lemma: a j-dim subspace of F_2^m holds at most C(j+1,2) vectors of weight 1 or 2
    (exhaustive over all subspaces for small (m, j) with m >= j + 1).
(2) Closed form C(B_s) = (s(s-1) - j(j+1)) / ((s-1)(s-2)) against the certified LP at s = 8.
"""
from fractions import Fraction
import numpy as np
import size_class_census as m

for (mm, j) in [(5, 2), (6, 3), (7, 3), (7, 4), (8, 3), (8, 4)]:
    H = m.subspaces(mm, j)
    pc = np.vectorize(lambda x: bin(int(x)).count("1"))(H)
    low = int(((pc >= 1) & (pc <= 2)).sum(axis=1).max())
    print(f"m={mm} j={j}: max #weight-1-or-2 = {low}, C(j+1,2) = {(j + 1) * j // 2}")
    assert low == (j + 1) * j // 2


def closed(s):
    j = s.bit_length() - 1
    return max(Fraction(1), Fraction(s * (s - 1) - j * (j + 1), (s - 1) * (s - 2)))


for s in (4, 8, 16, 32, 64, 1024):
    print("s =", s, "C(B_s) =", closed(s), round(float(closed(s)), 6))
S = [0] + [1 << i for i in range(7)]
C, p, w, Hs = m.C_value(7, S)
lo, up = m.certify(7, S, p, w, Hs)
print("LP s=8:", lo, up, "closed:", closed(8))
assert lo == up == closed(8)
