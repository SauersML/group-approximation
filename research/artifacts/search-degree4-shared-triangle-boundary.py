#!/usr/bin/env python3
"""Exact four-parameter shared-triangle screen using true group inverses."""

import importlib.util
from itertools import product
from pathlib import Path

SOURCE = Path(__file__).with_name("search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def elt(value, inverse):
    assert P.mul(value, inverse) == P.ONE
    assert P.mul(inverse, value) == P.ONE
    return value, inverse


def multiply(*elements):
    value = inverse = P.ONE
    for forward, backward in elements:
        value = P.mul(value, forward)
        inverse = P.mul(backward, inverse)
    return value, inverse


def inv(element):
    return element[1], element[0]


def reduce_word(word):
    stack = []
    for copy, element in word:
        if element[0] == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            element = multiply(stack.pop()[1], element)
            if element[0] == P.ONE:
                continue
        stack.append((copy, element))
    return tuple(stack)


def boundary(a, b, c, d):
    h_inverse = ((3, inv(a)), (2, inv(d)), (1, inv(c)), (0, inv(b)))
    b0 = ((0, a), (1, b), (2, c), (3, d))
    b1 = ((0, d), (1, a), (2, b), (3, c))
    b2 = ((0, c), (1, d), (2, a), (3, b))
    return reduce_word(h_inverse + b0 + h_inverse + b1 + h_inverse + b2)


def add(library, name, element):
    if all(old[0] != element[0] for _, old in library):
        library.append((name, element))


one = elt(P.ONE, P.ONE)
aa, bb = elt(P.A, P.A), elt(P.B, P.B)
cc, dd = elt(P.C, P.C), elt(P.D, P.D)
ee, qq = elt(P.E, P.E), elt(P.Q, P.Q)
pp, rr = elt(P.P, P.PINV), elt(P.R, P.RINV)
library = []
for name, element in (("1", one), ("a", aa), ("b", bb), ("c", cc),
                      ("d", dd), ("e", ee), ("q", qq), ("p", pp),
                      ("r", rr)):
    add(library, name, element)
    if name not in ("1", "a", "b", "c", "d", "e", "q"):
        add(library, name + "-", inv(element))

cd = multiply(cc, dd)
hmark = multiply(cd, cd)
for name, element in (("ab", multiply(aa, bb)), ("cd", cd),
                      ("dc", inv(cd)), ("h", hmark),
                      ("h-", inv(hmark))):
    add(library, name, element)

for length in range(2, 13):
    for first_name, first, second_name, second in (
            ("c", cc, "d", dd), ("d", dd, "c", cc)):
        name, element = "", one
        for index in range(length):
            if index % 2:
                name += second_name
                element = multiply(element, second)
            else:
                name += first_name
                element = multiply(element, first)
        add(library, name, element)

print("library", tuple(name for name, _ in library), flush=True)
tested = 0
for assignment in product(library, repeat=4):
    tested += 1
    word = boundary(*(entry[1] for entry in assignment))
    if len(word) == 1 and word[0][1][0] != P.ONE:
        print("HIT", tuple(entry[0] for entry in assignment),
              "copy", word[0][0], "terms", len(word[0][1][0]), flush=True)
        raise SystemExit(42)
    if tested % 10000 == 0:
        P.mul.cache_clear()
print("tested", tested, "hits 0", flush=True)
