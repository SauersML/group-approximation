"""Exact relative-piece audit for the six-relator Atlas quotient.

The ambient group is ``A8_1 * A8_2``.  This script extracts the five
transported boundary words and ``c_19243`` from the certified packet, reduces
them as free-product syllable words, symmetrizes by inversion and cyclic
rotation, and computes every common initial piece exactly.

No floating-point arithmetic is used.  The JSON output is a reproducible
certificate for the classical relative ``C'(lambda)`` tests.
"""

import json

import numpy as np

from atlas_asc_packet_build import interior_word, merge
from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_finite_quotient_scan import transported_word
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


INDICES = (0, 11, 30, 44, 55)


def inverse_syllable(syllable):
    factor, key = syllable
    matrix = np.frombuffer(bytes.fromhex(key), dtype=np.uint8).reshape(4, 4)
    return factor, matrix_key(gf2_inv(matrix)).hex()


def encode(word):
    return tuple((factor, matrix_key(matrix).hex()) for factor, matrix in word)


def multiply_keys(left, right):
    a = np.frombuffer(bytes.fromhex(left), dtype=np.uint8).reshape(4, 4)
    b = np.frombuffer(bytes.fromhex(right), dtype=np.uint8).reshape(4, 4)
    return matrix_key(gf2_mul(a, b)).hex()


IDENTITY = matrix_key(I4).hex()


def cyclic_reduce(encoded):
    word = list(encoded)
    while len(word) > 1 and word[0][0] == word[-1][0]:
        factor = word[0][0]
        key = multiply_keys(word[-1][1], word[0][1])
        word = word[1:-1]
        if key != IDENTITY:
            word.insert(0, (factor, key))
    return tuple(word)


def invert(encoded):
    return tuple(inverse_syllable(s) for s in reversed(encoded))


def rotations(encoded):
    return [encoded[i:] + encoded[:i] for i in range(len(encoded))]


def lcp(left, right):
    length = 0
    for a, b in zip(left, right):
        if a != b:
            break
        length += 1
    return length


def maximum_piece_prefix(prefix, self_variant, variants):
    return max((lcp(prefix, other) for other in variants
                if other != self_variant), default=0)


def minimum_piece_count(word, variants):
    """Minimum pieces covering one cyclic conjugate; None if impossible."""
    best = None
    for rotated in rotations(word):
        length = len(rotated)
        dp = [None] * (length + 1)
        dp[0] = 0
        for start in range(length):
            if dp[start] is None:
                continue
            tail = rotated[start:]
            self_variant = rotated[start:] + rotated[:start]
            cap = maximum_piece_prefix(tail, self_variant, variants)
            for size in range(1, cap + 1):
                value = dp[start] + 1
                if dp[start + size] is None or value < dp[start + size]:
                    dp[start + size] = value
        if dp[length] is not None and (best is None or dp[length] < best):
            best = dp[length]
    return best


def main():
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    boundary = boundary_words()
    words = {
        "s_%d" % index: cyclic_reduce(encode(merge(transported_word(
            boundary[index], alignment, alignment_inverse))))
        for index in INDICES
    }
    interior, _ = interior_word(alignment, alignment_inverse)
    words["c_19243"] = cyclic_reduce(encode(merge(interior)))

    symmetrized = {}
    sources = {}
    for name, word in words.items():
        for orientation, base in ((1, word), (-1, invert(word))):
            for shift, rotated in enumerate(rotations(base)):
                symmetrized.setdefault(rotated, len(symmetrized))
                sources.setdefault(rotated, []).append({
                    "relator": name,
                    "orientation": orientation,
                    "shift": shift,
                })

    variants = list(symmetrized)
    witnesses = []
    max_ratio = 0.0
    for i, left in enumerate(variants):
        for j in range(i + 1, len(variants)):
            right = variants[j]
            length = lcp(left, right)
            if not length:
                continue
            ratio = max(length / len(left), length / len(right))
            if ratio > max_ratio:
                max_ratio = ratio
                witnesses = []
            if ratio == max_ratio:
                witnesses.append({
                    "piece_syllables": length,
                    "left_length": len(left),
                    "right_length": len(right),
                    "left_source": sources[left],
                    "right_source": sources[right],
                    "piece": left[:length],
                })

    periodic = {}
    piece_counts = {}
    for name, word in words.items():
        periods = [period for period in range(1, len(word))
                   if len(word) % period == 0
                   and word == word[:period] * (len(word) // period)]
        periodic[name] = periods
        piece_counts[name] = minimum_piece_count(word, variants)

    print(json.dumps({
        "ambient": "A8_1 * A8_2",
        "relators": {name: {"syllable_length": len(word), "word": word}
                      for name, word in words.items()},
        "distinct_symmetrized_relators": len(variants),
        "maximum_piece_ratio": max_ratio,
        "maximum_piece_witnesses": witnesses,
        "strict_Cprime_1_6": max_ratio < 1 / 6,
        "strict_Cprime_1_4": max_ratio < 1 / 4,
        "minimum_piece_count_by_relator": piece_counts,
        "C_6": all(count is None or count >= 6
                   for count in piece_counts.values()),
        "C_4": all(count is None or count >= 4
                   for count in piece_counts.values()),
        "proper_power_linear_periods": periodic,
    }, indent=2))


if __name__ == "__main__":
    main()
