#!/usr/bin/env python3
"""Exact endpoint checks for the affine-Omega corner subgroup."""

import importlib.util
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("pictures", SOURCE)
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)

V4 = {M.ONE}
while True:
    enlarged = V4 | {M.mul(unit, generator)
                     for unit in V4 for generator in (M.A, M.E)}
    if enlarged == V4:
        break
    V4 = enlarged
assert len(V4) == 4
assert M.mul(M.A, M.E) == M.mul(M.E, M.A)

D8 = {M.ONE}
while True:
    enlarged = D8 | {M.mul(unit, generator)
                     for unit in D8 for generator in (M.C, M.Q)}
    if enlarged == D8:
        break
    D8 = enlarged
assert len(D8) == 8
assert M.power(M.mul(M.C, M.Q), 4) == M.ONE
assert M.power(M.mul(M.C, M.Q), 2) != M.ONE

for unit in (M.R, M.P, M.RINV, M.PINV):
    assert unit not in V4
    assert unit not in D8

LONG = {
    "H": ((0, M.R), (2, M.A), (1, M.C), (3, M.E),
          (2, M.Q), (3, M.P)),
    "K": ((1, M.A), (0, M.C), (2, M.E), (1, M.Q),
          (2, M.P), (3, M.R)),
    "L": ((0, M.P), (1, M.R), (3, M.A), (2, M.C)),
    "N": ((1, M.E), (0, M.Q), (1, M.P), (2, M.R)),
}


def inverse_unit(unit):
    return M.canon({(right, left) for left, right in unit})


def inverse(word):
    return tuple((copy, inverse_unit(unit))
                 for copy, unit in reversed(word))


letters = dict(LONG)
letters.update({name + "-": inverse(word) for name, word in LONG.items()})
inverse_name = {
    "H": "H-", "H-": "H", "K": "K-", "K-": "K",
    "L": "L-", "L-": "L", "N": "N-", "N-": "N",
}

checked_joins = 0
for left_name, left in letters.items():
    for right_name, right in letters.items():
        if left_name == inverse_name[right_name]:
            continue
        if left[-1][0] == right[0][0]:
            checked_joins += 1
            assert M.mul(left[-1][1], right[0][1]) != M.ONE

print("V4_size", len(V4), "D8_size", len(D8))
print("noninverse_same_copy_long_joins", checked_joins)
print("PASS: affine Omega corner endpoint checks are exact")
