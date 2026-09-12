#!/usr/bin/env python3
"""Test the endpoint-forced full-basis branch of the (1,5,7) template."""

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
basis = (("r", P.R), ("e", P.E), ("p", P.P),
         ("a", P.A), ("c", P.C))

tested = 0
for target_name, target in (("v", v), ("v-", vinv)):
    for assignment in permutations(basis):
        names = tuple(item[0] for item in assignment)
        g5, g6, g7, g10, g11 = (item[1] for item in assignment)
        g0 = inverse_unit(target)
        g1 = product(inverse_unit(g6), inverse_unit(g7))
        g2 = inverse_unit(g6)
        g3 = inverse_unit(g5)
        g4 = u
        g8 = g3
        g9 = u
        g12 = product(g0, g7, g6)
        slots = (g0, g1, g2, g3, g4, g5, g6,
                 g7, g8, g9, g10, g11, g12)
        hword = reduce_units(tuple((copy, slots[index]) for copy, index in
            ((0, 11), (1, 12), (2, 0), (1, 1), (0, 2), (1, 3),
             (0, 4), (1, 5), (0, 6), (1, 7), (2, 8), (1, 9),
             (2, 10))))
        hinv = inverse(hword)
        left = reduce_units(((0, g8),) + hword + ((2, g9),) + hinv +
                            ((0, g10), (1, g11), (2, g12)))
        right = reduce_units(((0, g3),) + hword + ((2, u),) + hinv +
                             ((0, g5),) + hword + ((2, g6),) + hinv +
                             ((0, g7), (1, g8), (0, g9),
                              (1, g10), (2, g11)))
        tested += 1
        if left == right:
            print("HIT", "target", target_name,
                  "free_names_g5_g6_g7_g10_g11", names,
                  "slots", slots, flush=True)
            raise SystemExit(42)

print("tested", tested)
print("hits 0")
