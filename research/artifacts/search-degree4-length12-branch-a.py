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


def multiply_words(*words):
    return reduce_word(sum(words, ()))


def multiply(*units):
    result = P.ONE
    for unit in units:
        result = P.mul(result, unit)
    return result


u, u_inverse = multiply(P.A, P.B), multiply(P.B, P.A)
v, v_inverse = multiply(P.C, P.D), multiply(P.D, P.C)
# Entries carry their algebraic group inverse.  The Bergman chart is a ring
# chart, not a unitary *-representation: transposing partial-bijection terms
# is NOT group inversion for elementary matrices.
library = (("1", P.ONE, P.ONE),
           ("h", P.TARGET, P.TARGET_INV),
           ("u", u, u_inverse), ("v", v, v_inverse),
           ("v-", v_inverse, v),
           ("a", P.A, P.A), ("b", P.B, P.B),
           ("c", P.C, P.C), ("d", P.D, P.D),
           ("r", P.R, P.RINV), ("p", P.P, P.PINV),
           ("e", P.E, P.E))

parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, choices=range(len(library)),
                    required=True)
args = parser.parse_args()

tested = projection_survivors = 0
for tail in product(library, repeat=5):
    assignment = (library[args.shard],) + tail
    names = tuple(entry[0] for entry in assignment)
    x, r, y, a, b, c = (entry[1] for entry in assignment)
    x_inverse, r_inverse, y_inverse, a_inverse, b_inverse, c_inverse = (
        entry[2] for entry in assignment)
    q = multiply(x_inverse, y_inverse)
    q_inverse = multiply(y, x)
    h_word = ((0, b), (1, c), (2, q), (3, a))
    h_inverse = ((3, a_inverse), (2, q_inverse),
                 (1, c_inverse), (0, b_inverse))
    b0 = ((0, a), (1, b), (2, c), (3, x_inverse))
    b1 = ((0, q), (1, a), (2, b), (3, c))
    e1_inverse = ((3, y_inverse),)
    e5_inverse = ((0, multiply(r_inverse, c_inverse)),)
    e4_inverse = ((3, b_inverse), (2, a_inverse),
                  (1, q_inverse), (0, r))
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
