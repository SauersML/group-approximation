#!/usr/bin/env python3
"""Exact projection-parametrized screen for length12 rank7 branch A.

Every element is stored with its actual multiplicative inverse.  The Bergman
chart is not unitary, so transposing a chart is not group inversion.
"""

import argparse
import importlib.util
from itertools import product as cartesian
from pathlib import Path

SOURCE = Path(__file__).with_name("search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def elt(value, inverse):
    assert P.mul(value, inverse) == P.ONE
    assert P.mul(inverse, value) == P.ONE
    return value, inverse


def mul(*elements):
    value = P.ONE
    inverse = P.ONE
    for forward, backward in elements:
        value = P.mul(value, forward)
        inverse = P.mul(backward, inverse)
    return value, inverse


def inv(element):
    return element[1], element[0]


ONE = elt(P.ONE, P.ONE)
A = elt(P.A, P.A)
B = elt(P.B, P.B)
C = elt(P.C, P.C)
D = elt(P.D, P.D)
R = elt(P.R, P.RINV)
PP = elt(P.P, P.PINV)
E = elt(P.E, P.E)
U = mul(A, B)
V = mul(C, D)
HMARK = mul(C, D, C, D)

library = (("1", ONE), ("h", HMARK), ("u", U), ("v", V),
           ("v-", inv(V)), ("a", A), ("b", B), ("c", C),
           ("d", D), ("r", R), ("p", PP), ("e", E))
involutions = tuple(item for item in library
                    if P.mul(item[1][0], item[1][0]) == P.ONE)


def reducew(word):
    stack = []
    for copy, element in word:
        if element[0] == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            element = mul(stack.pop()[1], element)
            if element[0] == P.ONE:
                continue
        stack.append((copy, element))
    return tuple(stack)


def invw(word):
    return tuple((copy, inv(element)) for copy, element in reversed(word))


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, choices=range(12), required=True)
args = parser.parse_args()
rname, r = library[args.shard]

tested = commuting = projection_survivors = 0
for (sname, s), (tname, t), (aname, a), (vname, vv) in cartesian(
        library, library, library, involutions):
    tested += 1
    if mul(vv, t)[0] != mul(t, vv)[0]:
        continue
    commuting += 1
    q = mul(inv(r), inv(t))
    b = mul(q, vv)
    c = mul(a, vv)
    H = reducew(((0, b), (1, c), (2, q), (3, a)))
    B0 = reducew(((0, a), (1, b), (2, c), (3, inv(r))))
    B1 = reducew(((0, q), (1, a), (2, b), (3, c)))
    E1 = ((3, t),)
    E5 = ((0, mul(c, s)),)
    E4 = reducew(((0, inv(s)), (1, q), (2, a), (3, b)))
    K = reducew(invw(H) + B0 + invw(H) + B1 + invw(E1) +
                invw(H) + invw(E5) + H + invw(E4) + H)
    projections = []
    for copy in range(4):
        value = ONE
        for index, element in K:
            if index == copy:
                value = mul(value, element)
        projections.append(value[0])
    if sum(value != P.ONE for value in projections) != 1:
        continue
    projection_survivors += 1
    if len(K) == 1 and K[0][1][0] != P.ONE:
        names = (rname, sname, tname, aname, vname)
        slots = (ONE, r, s, t, ONE, inv(t), inv(s), q,
                 a, b, c, inv(r))
        print("HIT", "r_s_t_a_v", names, "copy", K[0][0],
              "mark", K[0][1][0], "slots", tuple(x[0] for x in slots),
              "H", tuple((i, x[0]) for i, x in H),
              "K", tuple((i, x[0]) for i, x in K), flush=True)
        raise SystemExit(42)
    if tested % 10000 == 0:
        P.mul.cache_clear()

print("shard", args.shard, "r", rname, "tested", tested,
      "commuting", commuting, "projection_survivors", projection_survivors,
      "hits 0")
