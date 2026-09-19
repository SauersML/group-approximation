#!/usr/bin/env sage
"""Independent exact verification of the multiplicity-two 19243 escape."""

from sage.all import GF, identity_matrix

from atlas_a4_19243_component_localization import H6_LABELS, H18_LABELS, order
from atlas_a4_l44_bitpacked_screen import binary_matrix, relation_words
from atlas_a4_repeated_module_dataset import f4_to_f2, f2_matrix
from atlas_two_chart_search import factor_generators


ESCAPE = int("401004080301c030", 16)


def lift(value):
    return f2_matrix(f4_to_f2(binary_matrix(value)))


def conjugate(value, frame):
    return frame.inverse() * value * frame


def word_value(word, frame):
    value = identity_matrix(GF(2), 8)
    for factor, letter in word:
        letter = lift(letter)
        if factor == 2:
            letter = conjugate(letter, frame)
        value *= letter
    return value


def exact_a4(left, right):
    # <x,y | x^2=y^3=(xy)^3=1> is A4.  Here x and y retain exact
    # orders two and three, so the image cannot be the only proper quotient C3.
    return left**2 == identity and left != identity \
        and right**3 == identity and right != identity \
        and (left * right)**3 == identity


frame = f2_matrix(ESCAPE)
identity = identity_matrix(GF(2), 8)
assert frame.is_invertible()

for labels in (H6_LABELS, H18_LABELS):
    involutions = [lift(value) for value in labels if order(value) == 2]
    threes = [lift(value) for value in labels if order(value) == 3]
    moved_involutions = [conjugate(value, frame) for value in involutions]
    moved_threes = [conjugate(value, frame) for value in threes]
    assert all(exact_a4(left, right)
               for left in moved_involutions for right in threes)
    assert all(exact_a4(left, right)
               for left in involutions for right in moved_threes)

collision, q14 = relation_words()
assert word_value(collision, frame) == identity
assert word_value(q14, frame) != identity

generators = [lift(word[0][1]) for _, word in factor_generators()
              if word[0][0] == 1]
hub = conjugate(generators[4], frame) * generators[4]
assert hub != identity
assert hub**4 == identity and hub**2 != identity

print({
    "escape_conjugator": f"{ESCAPE:016x}",
    "all_packet_contexts_are_A4": True,
    "collision_19243": "identity",
    "q14": "nonidentity",
    "hub_opcode_order": 4,
})
