#!/usr/bin/env python3
"""Exact certificate: L_{1234} + L_{3456} lies in R^2(P_5) (braid arrangement A_4).

Planes (P_5 coordinates a_ij; puncture 6 = infinity):
  L_{1234} = P_4-circle on strands 1..4: a12=a34=x, a13=a24=y, a14=a23=-x-y  (basis p1: x=1,y=0; q1: x=0,y=1)
  L_{3456} = P_3-circle on strands 3,4,5: a34+a35+a45=0                  (basis p2: a34=1,a35=-1; q2: a34=1,a45=-1)
Checks, all over Z / Q exactly:
  (i)   p1^q1 = 0 and p2^q2 = 0 in A^2 (isotropy), so every product in L1^L2 is a cocycle for a in L1+L2;
  (ii)  at an integer point a = x p1 + y q1 + u p2 + w q2: a ^ (products) = 0 in A^3;
  (iii) rank_Q(a^A^1) <= 9 and rank_Q(a^A^1 + L1^L2) >= 10, giving dim H^2(A, a) >= 1 there and on a dense open set.
Usage: python3.11 os_resonance_cert.py
"""
import sys
from fractions import Fraction
sys.argv = [sys.argv[0], "5"]
import os_resonance as OS

E = OS.EDGES
IDX = OS.EIDX

def vec1(d):
    v = [0] * len(E)
    for e, c in d.items(): v[IDX[e]] += c
    return v

def wedge(u, basis_k, k):
    """u in A^1 (list over EDGES), x in A^k given as dict monomial->coef; returns dict monomial->coef in A^{k+1} (exact ints)."""
    out = {}
    for t, e in enumerate(E):
        if u[t] == 0: continue
        for m, c in basis_k.items():
            for mm, cc in OS.reduce((e,) + m).items():
                out[mm] = out.get(mm, 0) + u[t] * c * cc
    return {m: c for m, c in out.items() if c}

def as_dict1(u):
    return {(e,): u[t] for t, e in enumerate(E) if u[t]}

def rank_Q(vectors, dim_index):
    rows = [[Fraction(v.get(m, 0)) for m in dim_index] for v in vectors]
    rk = 0; ncol = len(dim_index)
    for col in range(ncol):
        piv = next((r for r in range(rk, len(rows)) if rows[r][col] != 0), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        pv = rows[rk][col]
        rows[rk] = [x / pv for x in rows[rk]]
        for r in range(len(rows)):
            if r != rk and rows[r][col] != 0:
                f = rows[r][col]; rows[r] = [x - f * y for x, y in zip(rows[r], rows[rk])]
        rk += 1
    return rk

p1 = vec1({(1, 2): 1, (3, 4): 1, (1, 4): -1, (2, 3): -1})
q1 = vec1({(1, 3): 1, (2, 4): 1, (1, 4): -1, (2, 3): -1})
p2 = vec1({(3, 4): 1, (3, 5): -1})
q2 = vec1({(3, 4): 1, (4, 5): -1})

iso1 = wedge(p1, as_dict1(q1), 1)
iso2 = wedge(p2, as_dict1(q2), 1)
print("isotropy p1^q1 == 0:", iso1 == {}, " p2^q2 == 0:", iso2 == {})

A2 = OS.BASIS[2]
products = [wedge(u, as_dict1(v), 1) for u in (p1, q1) for v in (p2, q2)]
for (x, y, u, w) in [(2, 3, 5, 7), (1, -4, 6, 11)]:
    a = [x * p + y * q + u * r + w * s for p, q, r, s in zip(p1, q1, p2, q2)]
    cocycle_ok = all(wedge(a, pr, 2) == {} for pr in products)
    coboundaries = [wedge(a, as_dict1([1 if t == k else 0 for t in range(len(E))]), 1) for k in range(len(E))]
    r1 = rank_Q(coboundaries, A2)
    r2 = rank_Q(coboundaries + products, A2)
    print(f"point {(x, y, u, w)}: products are cocycles: {cocycle_ok}; rank a^A^1 = {r1}; rank with L1^L2 = {r2}; "
          f"certified dim H^2 >= {r2 - 9 if r1 <= 9 else 'n/a'}")
print("DONE")
