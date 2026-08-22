#!/usr/bin/env python3
"""Search the exact four-parameter shared-triangle boundary in the Bergman chart."""

import importlib.util
from itertools import product
from pathlib import Path

SOURCE = Path(__file__).with_name("search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def inverse(unit):
    return P.canon({(right, left) for left, right in unit})


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


def boundary(a, b, c, d):
    # H=b_0 c_1 d_2 a_3 and B_i are the cyclic Latin-square rows.
    h_inverse = ((3, inverse(a)), (2, inverse(d)),
                 (1, inverse(c)), (0, inverse(b)))
    b0 = ((0, a), (1, b), (2, c), (3, d))
    b1 = ((0, d), (1, a), (2, b), (3, c))
    b2 = ((0, c), (1, d), (2, a), (3, b))
    return reduce_word(h_inverse + b0 + h_inverse + b1 + h_inverse + b2)


def add(library, name, unit):
    if all(old != unit for _, old in library):
        library.append((name, unit))


library = []
for name, unit in (("1", P.ONE), ("a", P.A), ("b", P.B),
                   ("c", P.C), ("d", P.D), ("e", P.E),
                   ("p", P.P), ("r", P.R)):
    add(library, name, unit)
    if name not in ("1", "a", "b", "c", "d", "e"):
        add(library, name + "-", inverse(unit))

for name, unit in (("ab", P.mul(P.A, P.B)),
                   ("cd", P.mul(P.C, P.D)),
                   ("dc", P.mul(P.D, P.C)),
                   ("h", P.TARGET), ("h-", P.TARGET_INV)):
    add(library, name, unit)

print("library", tuple(name for name, _ in library), flush=True)
tested = 0
for assignment in product(library, repeat=4):
    tested += 1
    word = boundary(*(entry[1] for entry in assignment))
    for copy in range(4):
        if word == ((copy, P.TARGET),):
            print("HIT", tuple(entry[0] for entry in assignment),
                  "copy", copy, flush=True)
        if word == ((copy, P.TARGET_INV),):
            print("HIT_INV", tuple(entry[0] for entry in assignment),
                  "copy", copy, flush=True)
print("tested", tested, flush=True)

