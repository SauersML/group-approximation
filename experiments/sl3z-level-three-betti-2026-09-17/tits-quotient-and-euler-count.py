#!/usr/bin/env python3
"""Sanity checks for sl3z-level-three-congruence-subgroup-has-b2-26.

1. |SL_3(F_3)| = 5616 and |B(F_3)| = 108, so SL_3(F_3) has 52 = 5616/108 flags.
2. The Tits building T_3(F_3) is the point-line incidence graph of PG(2,3):
   13 points, 13 lines, 52 incident pairs, connected.  Its first Betti number is
   52 - 26 + 1 = 27 = 3^3, the rank of St_3(F_3).  The group H_1 is computed
   exactly over Z (Smith normal form of the boundary map) to confirm it is free.
3. Reduction mod 3 of primitive vectors: the image of the primitive vectors of Z^3
   with entries in [-R, R] meets every nonzero vector of F_3^3 (consistency of the
   bijection {Gamma(3)-orbits of lines} <-> P^2(F_3); not a proof, a spot check).
4. Euler count: with b_0 = 1, b_1 = 0, b_3 = 27, b_q = 0 for q >= 4 and chi = 0,
   b_2 = 26.
"""
import itertools
from math import gcd

from sympy import Matrix
from sympy.matrices.normalforms import smith_normal_form
from sympy import ZZ

p = 3
F = range(p)

# 1. group orders
sl3 = 1
for i in range(3):
    sl3 *= p**3 - p**i
sl3 //= p - 1
borel = (p - 1) ** 2 * p**3
assert sl3 == 5616 and borel == 108 and sl3 // borel == 52

# 2. incidence graph of PG(2,3)
def normalize(v):
    for x in v:
        if x % p:
            inv = pow(x, -1, p)
            return tuple((inv * y) % p for y in v)
    raise ValueError

vecs = [v for v in itertools.product(F, repeat=3) if any(v)]
points = sorted({normalize(v) for v in vecs})
lines = sorted({normalize(v) for v in vecs})  # lines of P^2 = dual points
assert len(points) == 13 and len(lines) == 13
edges = [(a, b) for a in points for b in lines
         if sum(x * y for x, y in zip(a, b)) % p == 0]
assert len(edges) == 52
V = [("P", a) for a in points] + [("L", b) for b in lines]
idx = {v: i for i, v in enumerate(V)}
# connectivity
adj = {i: set() for i in range(len(V))}
for a, b in edges:
    i, j = idx[("P", a)], idx[("L", b)]
    adj[i].add(j)
    adj[j].add(i)
seen, stack = {0}, [0]
while stack:
    u = stack.pop()
    for w in adj[u] - seen:
        seen.add(w)
        stack.append(w)
assert len(seen) == 26
# exact H_1 over Z: kernel of boundary d1: Z^52 -> Z^26
d1 = Matrix.zeros(len(V), len(edges))
for k, (a, b) in enumerate(edges):
    d1[idx[("L", b)], k] = 1
    d1[idx[("P", a)], k] = -1
rank_d1 = d1.rank()
snf = smith_normal_form(d1, domain=ZZ)
diag = [snf[i, i] for i in range(min(snf.shape)) if snf[i, i] != 0]
assert rank_d1 == 25 and all(abs(x) == 1 for x in diag)  # coker d1 = Z, free
b1_graph = len(edges) - rank_d1
assert b1_graph == 27 == p**3

# 3. reduction of primitive vectors hits every nonzero vector of F_3^3
R = 3
hit = set()
for v in itertools.product(range(-R, R + 1), repeat=3):
    if any(v) and gcd(gcd(abs(v[0]), abs(v[1])), abs(v[2])) == 1:
        hit.add(tuple(x % p for x in v))
assert len(hit) == 26

# 4. Euler count
b0, b1, b3 = 1, 0, b1_graph
b2 = b3 - b0 + b1  # from 1 - b1 + b2 - b3 = 0
assert b2 == 26
print("|SL3(F3)|=%d |B(F3)|=%d flags=%d" % (sl3, borel, sl3 // borel))
print("PG(2,3) incidence graph: V=26 E=52 connected, H_1 free of rank %d" % b1_graph)
print("Betti numbers of Gamma(3): b0=1 b1=0 b2=%d b3=%d" % (b2, b3))
