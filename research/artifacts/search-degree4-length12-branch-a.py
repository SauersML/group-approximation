#!/usr/bin/env python3
"""Exact adaptive one-copy screen for the best length-12 branch A."""

import argparse
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


def inverse_word(word):
    return tuple((copy, inverse(unit)) for copy, unit in reversed(word))


def multiply_words(*words):
    return reduce_word(sum(words, ()))


def multiply(*units):
    result = P.ONE
    for unit in units:
        result = P.mul(result, unit)
    return result


u, v = multiply(P.A, P.B), multiply(P.C, P.D)
library = (("1", P.ONE), ("h", P.TARGET), ("u", u), ("v", v),
           ("v-", inverse(v)), ("a", P.A), ("b", P.B),
           ("c", P.C), ("d", P.D), ("r", P.R), ("p", P.P),
           ("e", P.E))

parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, choices=range(len(library)),
                    required=True)
args = parser.parse_args()

tested = projection_survivors = 0
for tail in product(library, repeat=5):
    assignment = (library[args.shard],) + tail
    names = tuple(entry[0] for entry in assignment)
    x, r, y, a, b, c = (entry[1] for entry in assignment)
    q = multiply(inverse(x), inverse(y))
    h_word = ((0, b), (1, c), (2, q), (3, a))
    h_inverse = inverse_word(h_word)
    b0 = ((0, a), (1, b), (2, c), (3, inverse(x)))
    b1 = ((0, q), (1, a), (2, b), (3, c))
    e1_inverse = ((3, inverse(y)),)
    e5_inverse = ((0, inverse(multiply(c, r))),)
    e4_inverse = ((3, inverse(b)), (2, inverse(a)),
                  (1, inverse(q)), (0, r))
    boundary = multiply_words(h_inverse, b0, h_inverse, b1,
                              e1_inverse, h_inverse, e5_inverse,
                              h_word, e4_inverse, h_word)
    tested += 1
    projections = []
    for copy in range(4):
        value = P.ONE
        for factor_copy, unit in boundary:
            if factor_copy == copy:
                value = P.mul(value, unit)
        projections.append(value)
    nontrivial = [(copy, value) for copy, value in enumerate(projections)
                  if value != P.ONE]
    if len(nontrivial) != 1:
        continue
    projection_survivors += 1
    copy, mark = nontrivial[0]
    if boundary == ((copy, mark),):
        print("HIT", names, "copy", copy, "mark_terms", len(mark),
              flush=True)
        raise SystemExit(42)

print("shard", args.shard, "x", library[args.shard][0], "tested", tested,
      "projection_survivors", projection_survivors, "hits 0", flush=True)

