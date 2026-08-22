#!/usr/bin/env python3
"""Exact metacyclic countermodel to the shared-triangle retraction screen."""

import importlib.util
from pathlib import Path

SOURCE = Path(__file__).with_name("search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def permutation(action):
    return P.canon({(P.prefix(action(index) + 1), P.prefix(index + 1))
                    for index in range(20)})


def inverse(unit):
    return P.canon({(right, left) for left, right in unit})


def power(unit, exponent):
    result = P.ONE
    for _ in range(exponent):
        result = P.mul(result, unit)
    return result


def reduce_word(word):
    stack = []
    for copy, unit in word:
        if unit == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            unit = P.mul(stack.pop()[1], unit)
            if unit == P.ONE:
                continue
        stack.append((copy, unit))
    return tuple(stack)


def retract(word, copy):
    result = P.ONE
    for factor_copy, unit in word:
        if factor_copy == copy:
            result = P.mul(result, unit)
    return result


w = permutation(lambda index: (index + 1) % 16 if index < 16 else index)
z = permutation(lambda index: (13 * index + 1) % 16
                if index < 16 else index)
assert power(w, 16) == P.ONE
assert P.mul(P.mul(z, w), inverse(z)) == power(w, 13)
assert power(z, 4) == power(w, 12)
assert power(w, 8) != P.ONE

# a=1, d=w, c=wz, b=wz^-1w realizes the projection equations.
a = P.ONE
d = w
c = P.mul(w, z)
b = P.mul(P.mul(w, inverse(z)), w)
h_inverse = ((3, inverse(a)), (2, inverse(d)),
             (1, inverse(c)), (0, inverse(b)))
b0 = ((0, a), (1, b), (2, c), (3, d))
b1 = ((0, d), (1, a), (2, b), (3, c))
b2 = ((0, c), (1, d), (2, a), (3, b))
boundary = reduce_word(h_inverse + b0 + h_inverse + b1 + h_inverse + b2)

exponents = []
for copy in range(4):
    image = retract(boundary, copy)
    exponents.append(next(exponent for exponent in range(16)
                          if image == power(w, exponent)))
print("retraction exponents", tuple(exponents))
print("reduced free-product blocks", len(boundary))
assert exponents == [8, 0, 0, 0]
assert len(boundary) == 16
assert boundary != ((0, power(w, 8)),)

