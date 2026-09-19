#!/usr/bin/env python3
"""Symbolic common multiple of two generic linear forms t_p, t_q in x_0, x_1, x_2 (Q_1), degree n = 2."""
import itertools, sympy as sp
from qk_linalg import left_mult, monomials

n, L = 2, 4
a0, b0, c0, a1, b1, c1 = sp.symbols('a0 b0 c0 a1 b1 c1')
V = monomials(n, L)
A = monomials(n + 1, L)
Aidx = {m: i for i, m in enumerate(A)}
t0 = (a0, b0, c0)
t1 = (a1, b1, c1)
M = sp.zeros(len(A), 2 * len(V))
for col, w in enumerate(V):
    for j in range(3):
        M[Aidx[left_mult(j, w)], col] += t0[j]
        M[Aidx[left_mult(j, w)], len(V) + col] -= t1[j]
ns = M.nullspace(simplify=True)
print("nullity", len(ns))
for v in ns:
    v = sp.simplify(v * sp.lcm([sp.fraction(sp.together(x))[1] for x in v]))
    u0 = {V[i]: sp.factor(v[i]) for i in range(len(V)) if v[i] != 0}
    u1 = {V[i]: sp.factor(-v[len(V) + i]) for i in range(len(V)) if v[len(V) + i] != 0}
    print("u0:")
    for w, c in u0.items():
        print("  ", w, c)
    print("u1:")
    for w, c in u1.items():
        print("  ", w, c)
    # product
    prod = {}
    for w, c in u0.items():
        for j in range(3):
            m = left_mult(j, w)
            prod[m] = sp.expand(prod.get(m, 0) + t0[j] * c)
    print("w = t0 u0:")
    for m, c in sorted(prod.items()):
        if sp.simplify(c) != 0:
            print("  ", m, sp.factor(c))
