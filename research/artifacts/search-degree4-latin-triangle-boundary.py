#!/usr/bin/env python3
"""Exact four-parameter screen for the rank-surviving d4 carrier triangle."""

import importlib.util
from itertools import product as cartesian
from pathlib import Path

SOURCE = Path(__file__).with_name("search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def invu(unit):
    return P.canon({(right, left) for left, right in unit})


def reducew(word):
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


def invw(word):
    return tuple((copy, invu(unit)) for copy, unit in reversed(word))


def prod(*units):
    out = P.ONE
    for unit in units:
        out = P.mul(out, unit)
    return out


u, v, h = prod(P.A, P.B), prod(P.C, P.D), P.TARGET
library = (("1", P.ONE), ("h", h), ("u", u),
           ("v", v), ("v-", invu(v)), ("a", P.A), ("b", P.B),
           ("c", P.C), ("d", P.D), ("r", P.R), ("p", P.P), ("e", P.E))

tested = projection_survivors = 0
for assignment in cartesian(library, repeat=4):
    names = tuple(item[0] for item in assignment)
    a, b, c, d = (item[1] for item in assignment)
    H = reducew(((0, b), (1, c), (2, d), (3, a)))
    B0 = reducew(((0, a), (1, b), (2, c), (3, d)))
    B1 = reducew(((0, d), (1, a), (2, b), (3, c)))
    B2 = reducew(((0, c), (1, d), (2, a), (3, b)))
    F = reducew(invw(H) + B0 + invw(H) + B1 + invw(H) + B2)
    tested += 1
    for copy in range(4):
        if F == ((copy, h),):
            print("HIT", "copy", copy, "a_b_c_d", names,
                  "H", H, "B0", B0, "B1", B1, "B2", B2,
                  "F", F, flush=True)
            raise SystemExit(42)
    projected = []
    for copy in range(4):
        value = P.ONE
        for index, unit in F:
            if index == copy:
                value = P.mul(value, unit)
        projected.append(value)
    if sum(value == h for value in projected) == 1 and sum(
            value == P.ONE for value in projected) == 3:
        projection_survivors += 1
        print("PROJECTION_SURVIVOR", names, flush=True)

print("tested", tested, "projection_survivors", projection_survivors, "hits 0")
