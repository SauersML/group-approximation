#!/usr/bin/env python3
"""Solve the parameterized length-eleven (1,5,5) holonomy equation.

The source/target holonomies are imposed symbolically first.  Six remaining
slots range over permutations containing the full generating basis
(r,e,p,a,c) and one short compound.  The sole common-carrier equation is then
tested in the faithful Bergman/free-product normal form.
"""

import importlib.util
from itertools import permutations
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def inverse_unit(unit):
    return P.canon({(right, left) for left, right in unit})


def inverse(word):
    return tuple((copy, inverse_unit(unit))
                 for copy, unit in reversed(word))


def reduce_units(factors):
    stack = []
    for copy, unit in factors:
        if unit == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            unit = P.mul(stack.pop()[1], unit)
            if unit == P.ONE:
                continue
        stack.append((copy, unit))
    return tuple(stack)


def product(*units):
    result = P.ONE
    for unit in units:
        result = P.mul(result, unit)
    return result


u = product(P.A, P.B)
v = product(P.C, P.D)
vinv = inverse_unit(v)
assert product(u, u) == P.ONE
assert product(v, v) == P.TARGET

basis = (("r", P.R), ("e", P.E), ("p", P.P),
         ("a", P.A), ("c", P.C))
extras = (("1", P.ONE), ("u", u), ("v", v), ("v-", vinv),
          ("h", P.TARGET), ("b", P.B), ("d", P.D))

tested = 0
for target_name, target in (("v", v), ("v-", vinv)):
    g0 = inverse_unit(target)
    for extra in extras:
        for assignment in permutations(basis + (extra,)):
            names = tuple(item[0] for item in assignment)
            g4, g5, g6, g7, g8, g9 = (item[1] for item in assignment)
            g3 = u
            g2 = inverse_unit(g4)
            g1 = product(g2, inverse_unit(g5))
            g10 = product(g0, g5, g4)
            slots = (g0, g1, g2, g3, g4, g5,
                     g6, g7, g8, g9, g10)
            hword = reduce_units(tuple((copy, slots[index]) for copy, index in
                ((0, 9), (1, 10), (2, 0), (1, 1), (0, 2), (1, 3),
                 (0, 4), (1, 5), (2, 6), (1, 7), (2, 8))))
            hinv = inverse(hword)
            left = reduce_units(((0, g6),) + hword + ((2, g7),) + hinv +
                                ((0, g8), (1, g9), (2, g10)))
            right = reduce_units(((0, u),) + hword + ((2, g4),) + hinv +
                                 ((0, g5), (1, g6), (0, g7),
                                  (1, g8), (2, g9)))
            tested += 1
            if left == right:
                print("HIT", "target", target_name,
                      "free_names_g4_to_g9", names,
                      "derived", {"g0": target_name + "-",
                                  "g1": "g4^-1 g5^-1",
                                  "g2": "g4^-1", "g3": "u",
                                  "g10": target_name + "- g5 g4"},
                      "hword", hword, flush=True)
                raise SystemExit(42)

print("tested", tested)
print("hits 0")
