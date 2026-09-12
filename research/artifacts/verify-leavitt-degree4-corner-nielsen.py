#!/usr/bin/env python3
"""Exact finite checks used by the degree-four corner Nielsen proof."""

import importlib.util
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


V4 = {M.ONE, M.A, M.B, M.mul(M.A, M.B)}
assert len(V4) == 4
assert M.mul(M.A, M.B) == M.mul(M.B, M.A)

D8 = {M.ONE}
changed = True
while changed:
    changed = False
    for element in tuple(D8):
        for generator in (M.C, M.D):
            product = M.mul(element, generator)
            if product not in D8:
                D8.add(product)
                changed = True
assert len(D8) == 8
assert M.power(M.mul(M.C, M.D), 4) == M.ONE
assert M.power(M.mul(M.C, M.D), 2) != M.ONE

for unit in (M.R, M.E, M.P, M.RINV, M.PINV):
    assert unit not in V4
    assert unit not in D8

LONG = {
    "H": ((0, M.R), (1, M.E), (2, M.A), (1, M.C),
          (3, M.B), (2, M.D), (3, M.P)),
    "K": ((0, M.E), (1, M.A), (0, M.C), (2, M.B),
          (1, M.D), (2, M.P), (3, M.R)),
    "L": ((0, M.P), (1, M.R), (2, M.E), (3, M.A), (2, M.C)),
    "M": ((1, M.B), (0, M.D), (1, M.P), (2, M.R), (3, M.E)),
}
INVERSE_UNIT = {
    M.R: M.RINV, M.E: M.E, M.A: M.A, M.C: M.C,
    M.B: M.B, M.D: M.D, M.P: M.PINV,
}


def inverse(word):
    return tuple((copy, INVERSE_UNIT[unit]) for copy, unit in reversed(word))


LETTERS = dict(LONG)
LETTERS.update({name + "-": inverse(word) for name, word in LONG.items()})
INVERSE_NAME = {
    "H": "H-", "H-": "H", "K": "K-", "K-": "K",
    "L": "L-", "L-": "L", "M": "M-", "M-": "M",
}

checked_joins = 0
for left_name, left in LETTERS.items():
    for right_name, right in LETTERS.items():
        if left_name == INVERSE_NAME[right_name]:
            continue
        if left[-1][0] == right[0][0]:
            checked_joins += 1
            assert M.mul(left[-1][1], right[0][1]) != M.ONE

print("V4_size=4 D8_size=8")
print("endpoint_membership_exclusions=10")
print(f"noninverse_same_copy_long_joins={checked_joins}")
print("PASS: all Nielsen endpoint checks are exact in Bergman normal form")
