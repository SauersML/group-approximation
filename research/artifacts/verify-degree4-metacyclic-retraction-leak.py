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


def inverse_word(word):
    return tuple((copy, inverse(unit)) for copy, unit in reversed(word))


def multiply_words(*words):
    return reduce_word(sum(words, ()))


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

# Audit all six cyclic/inverse orientations on each of the three triangle
# faces.  The residual factor triples are (H,H^-1 B_i,H^-1) for this family.
h_word = ((0, b), (1, c), (2, d), (3, a))
h_word_inverse = inverse_word(h_word)
factor_triples = tuple((h_word, multiply_words(h_word_inverse, row),
                        h_word_inverse) for row in (b0, b1, b2))
canonical = (("P", 1), ("A", 1), ("Q", 1)), \
            (("Q", -1), ("B", 1), ("R", 1)), \
            (("R", -1), ("C", 1), ("P", -1))


def orientations(tokens):
    inverse_tokens = tuple((name, -exponent)
                           for name, exponent in reversed(tokens))
    return tuple(word[offset:] + word[:offset]
                 for word in (tokens, inverse_tokens)
                 for offset in range(3))


orientation_sets = tuple(orientations(tokens) for tokens in canonical)
linked, marked, linked_data = 0, [], []
from itertools import product
for choices in product(range(6), repeat=3):
    values = {}
    for face, choice in enumerate(choices):
        for token, factor in zip(orientation_sets[face][choice],
                                 factor_triples[face]):
            name, exponent = token
            canonical_value = factor if exponent == 1 else inverse_word(factor)
            values.setdefault(name, []).append(canonical_value)
    if any(values[carrier][0] != values[carrier][1]
           for carrier in ("P", "Q", "R")):
        continue
    linked += 1
    coefficients = tuple(values[name][0] for name in ("A", "B", "C"))
    mark = multiply_words(*coefficients)
    linked_data.append((choices, len(mark)))
    if len(mark) == 1 and mark[0][1] != P.ONE:
        marked.append((choices, mark[0][0], mark[0][1] == power(w, 8)))
print("linked orientations", linked)
print("linked orientation/block counts", tuple(linked_data))
print("one-copy nonidentity orientations", tuple(marked))
assert not marked


def scan_parameters(a_value, b_value, c_value, d_value):
    h_value = ((0, b_value), (1, c_value),
               (2, d_value), (3, a_value))
    h_value_inverse = inverse_word(h_value)
    rows = (((0, a_value), (1, b_value), (2, c_value), (3, d_value)),
            ((0, d_value), (1, a_value), (2, b_value), (3, c_value)),
            ((0, c_value), (1, d_value), (2, a_value), (3, b_value)))
    triples = tuple((h_value, multiply_words(h_value_inverse, row),
                     h_value_inverse) for row in rows)
    found = []
    for choices in product(range(6), repeat=3):
        values = {}
        for face, choice in enumerate(choices):
            for token, factor in zip(orientation_sets[face][choice],
                                     triples[face]):
                name, exponent = token
                canonical_value = (factor if exponent == 1
                                   else inverse_word(factor))
                values.setdefault(name, []).append(canonical_value)
        if any(values[carrier][0] != values[carrier][1]
               for carrier in ("P", "Q", "R")):
            continue
        mark = multiply_words(*(values[name][0] for name in ("A", "B", "C")))
        if len(mark) == 1 and mark[0][1] != P.ONE:
            found.append((choices, mark))
    return found


# Exhaust the free gauge b in the whole finite metacyclic packet <w,z>.
packet = {P.ONE}
frontier = [P.ONE]
while frontier:
    old = frontier.pop()
    for generator in (w, z, inverse(w), inverse(z)):
        new = P.mul(old, generator)
        if new not in packet:
            packet.add(new)
            frontier.append(new)
x = P.mul(power(w, 2), z)
gauge_hits = []
for gauge in packet:
    a_gauge = P.mul(gauge, x)
    b_gauge = gauge
    d_gauge = P.mul(a_gauge, w)
    c_gauge = P.mul(d_gauge, z)
    gauge_hits.extend(scan_parameters(a_gauge, b_gauge, c_gauge, d_gauge))
print("metacyclic gauge size", len(packet))
print("metacyclic gauge one-copy hits", len(gauge_hits))
assert len(packet) == 64
assert not gauge_hits

# The packet is contained in the affine normalizer of the regular 16-cycle.
# Exhaust the full 128 affine permutations as gauges as a sharper normalizer
# screen (including the four unit slopes outside <13>).
affine_hits = []
for slope in range(1, 16, 2):
    for shift in range(16):
        gauge = permutation(lambda index, slope=slope, shift=shift:
                            (slope * index + shift) % 16
                            if index < 16 else index)
        a_gauge = P.mul(gauge, x)
        d_gauge = P.mul(a_gauge, w)
        c_gauge = P.mul(d_gauge, z)
        affine_hits.extend(scan_parameters(a_gauge, gauge, c_gauge, d_gauge))
print("affine-normalizer gauge size", 128)
print("affine-normalizer one-copy hits", len(affine_hits))
assert not affine_hits
