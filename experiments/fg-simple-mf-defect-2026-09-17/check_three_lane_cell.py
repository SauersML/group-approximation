#!/usr/bin/env python3
"""Exact checks for the three-lane cell group Delta of
research/fg-simple-mf-group-with-full-compression-defect-proof.md.

Omega = Z x Z/3.  rho(i,j) = (i, j+1).  t(i,j) = (i + d_j, j), d = (1, 0, -1).
b = t rho^{-1}.  Maps are stored as Python functions on Omega and compared
on a window.  Elements of Q = <t, rho> are lane translations composed with
lane rotations, so agreement on one point per lane already determines them;
the finitary cycles used here are supported inside the window.

Checks:
 1. b^3 = 1 and b != 1, and t = b rho (so t is a product of two elements
    of order 3).
 2. The cell: u = t, l = ((0,0),(1,0),(2,0)), c = ((-3,0),(-2,0),(-1,0)).
    c commutes with u^k l u^-k for 0 <= k < K, and [u c u^-1, l] != 1.
 3. The generation lemma on a window: the translates T_v B, B = {0,1} x Z/3,
    v in a box of the sum-zero lattice, generate the full alternating group
    of their union (checked by group order with sympy).
"""
from itertools import product
from math import factorial

from sympy.combinatorics import Permutation, PermutationGroup

d = (1, 0, -1)


def rho(p):
    i, j = p
    return (i, (j + 1) % 3)


def rho_inv(p):
    i, j = p
    return (i, (j - 1) % 3)


def t(p):
    i, j = p
    return (i + d[j], j)


def t_inv(p):
    i, j = p
    return (i - d[j], j)


def compose(*fs):
    """compose(f, g)(p) = f(g(p))."""
    def h(p):
        for f in reversed(fs):
            p = f(p)
        return p
    return h


def ident(p):
    return p


WINDOW = [(i, j) for i in range(-30, 31) for j in range(3)]


def same(f, g):
    return all(f(p) == g(p) for p in WINDOW)


b = compose(t, rho_inv)
assert same(compose(b, b, b), ident), "b^3 != 1"
assert not same(b, ident), "b == 1"
assert same(compose(b, rho), t), "t != b rho"
print("check 1 ok: b = t rho^-1 has order 3 and t = b rho")


def cycle(points):
    pts = list(points)
    m = {pts[k]: pts[(k + 1) % len(pts)] for k in range(len(pts))}
    return lambda p: m.get(p, p)


def conj(g, g_inv, f):
    return compose(g, f, g_inv)


def power(f, k):
    return compose(*([f] * k)) if k > 0 else ident


l = cycle([(0, 0), (1, 0), (2, 0)])
c = cycle([(-3, 0), (-2, 0), (-1, 0)])
K = 20
for k in range(K):
    lk = conj(power(t, k), power(t_inv, k), l)
    assert same(compose(c, lk), compose(lk, c)), f"c fails to commute with l_{k}"
ucu = conj(t, t_inv, c)
assert not same(compose(ucu, l), compose(l, ucu)), "[u c u^-1, l] = 1"
print(f"check 2 ok: c commutes with l_k for 0 <= k < {K}, [u c u^-1, l] != 1")

# check 3: generation lemma on a window
lattice = [(a, bb, -a - bb) for a in range(-1, 2) for bb in range(-1, 2)]
B = [(i, j) for i in (0, 1) for j in range(3)]


def translate(v, p):
    i, j = p
    return (i + v[j], j)


translates = [[translate(v, p) for p in B] for v in lattice]
union = sorted({p for T in translates for p in T})
index = {p: n for n, p in enumerate(union)}
gens = []
for T in translates:
    for x, y, z in product(T, repeat=3):
        if len({x, y, z}) == 3:
            gens.append(Permutation([[index[x], index[y], index[z]]],
                                    size=len(union)))
G = PermutationGroup(gens)
n = len(union)
assert G.order() == factorial(n) // 2, (G.order(), n)
print(f"check 3 ok: {len(lattice)} translates of B generate Alt({n}) "
      "on their union")
print("all checks passed")
