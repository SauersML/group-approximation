#!/usr/bin/env sage
"""Tiny m=3 test: permutation gauges on the H6-trivial carrier only."""

import itertools
import json

from sage.all import GF, Matrix, identity_matrix

from atlas_a4_19243_component_localization import H6_LABELS, H18_LABELS, order
from atlas_a4_l44_bitpacked_screen import relation_words


FIELD = GF(2)
MULTIPLICITY = 3
DIMENSION = 12
U0_BITS = 0x2841


def matrix4(bits):
    return Matrix(FIELD, 4, 4,
                  [(bits >> (4 * i + j)) & 1 for i in range(4) for j in range(4)])


def lift(value):
    return Matrix(FIELD, value).tensor_product(identity_matrix(FIELD, MULTIPLICITY))


def gauge(permutation):
    value = identity_matrix(FIELD, DIMENSION)
    trivial_indices = list(range(0, 3)) + list(range(9, 12))
    for row in trivial_indices:
        for column in trivial_indices:
            value[row, column] = 0
    for column, image in enumerate(permutation):
        value[trivial_indices[image], trivial_indices[column]] = 1
    return value


def evaluate(word, frame):
    value = identity_matrix(FIELD, DIMENSION)
    inverse = frame.inverse()
    for factor, letter in word:
        letter = lift(letter)
        if factor == 2:
            letter = inverse * letter * frame
        value *= letter
    return value


base = matrix4(U0_BITS).tensor_product(identity_matrix(FIELD, MULTIPLICITY))
h18_i = [lift(value) for value in H18_LABELS if order(value) == 2]
h18_t = [lift(value) for value in H18_LABELS if order(value) == 3]
collision_word, q14_word = relation_words()
identity = identity_matrix(FIELD, DIMENSION)

packet = collision = q14 = joint = 0
rank_pairs = {}
first_joint = None
for permutation in itertools.permutations(range(6)):
    frame = gauge(permutation) * base
    inverse = frame.inverse()
    moved_i = [inverse * value * frame for value in h18_i]
    moved_t = [inverse * value * frame for value in h18_t]
    if not all((left * right)**3 == identity
               for left in moved_i for right in h18_t):
        continue
    if not all((left * right)**3 == identity
               for left in h18_i for right in moved_t):
        continue
    packet += 1
    collision_value = evaluate(collision_word, frame)
    q14_value = evaluate(q14_word, frame)
    collision_good = collision_value == identity
    q14_good = q14_value == identity
    collision += collision_good
    q14 += q14_good
    joint += collision_good and q14_good
    ranks = ((collision_value - identity).rank(), (q14_value - identity).rank())
    rank_pairs[ranks] = rank_pairs.get(ranks, 0) + 1
    if collision_good and q14_good and first_joint is None:
        first_joint = permutation

print(json.dumps({
    "ansatz": "m=3 H6-trivial-carrier permutation gauges",
    "gauges": 720,
    "packet_survivors": packet,
    "collision_survivors": collision,
    "q14_survivors": q14,
    "joint_survivors": joint,
    "first_joint_permutation": first_joint,
    "defect_rank_pairs": {f"{a},{b}": count
                          for (a, b), count in sorted(rank_pairs.items())},
}, indent=2, sort_keys=True))
