"""Evaluate the atlas collision words in the candidate ``A8 *_H A8``.

The second factor is first transported through the unique classical inner
alignment ``k0``.  In those coordinates both copies of

    H = diag(GL(3,2), 1)

are identified literally.  A reduced free-product word represents the
identity in the amalgam exactly when elementary absorption of every
``H``-syllable reduces it to the empty word.  This is the standard normal
form theorem for a free product with amalgamation and uses only exact
``F_2`` matrix arithmetic.
"""

import json
from collections import Counter

import numpy as np

from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


def lies_in_h(matrix):
    expected = I4.copy()
    expected[:3, :3] = matrix[:3, :3]
    return np.array_equal(matrix, expected)


def multiply_adjacent(word):
    output = []
    for factor, matrix in word:
        if np.array_equal(matrix, I4):
            continue
        if output and output[-1][0] == factor:
            product = gf2_mul(output[-1][1], matrix)
            output.pop()
            if not np.array_equal(product, I4):
                output.append((factor, product))
        else:
            output.append((factor, matrix))
    return output


def amalgam_normal_form(word):
    current = multiply_adjacent(word)
    while len(current) > 1:
        position = next((index for index, (_factor, matrix)
                         in enumerate(current) if lies_in_h(matrix)), None)
        if position is None:
            break
        if position == 0:
            h = current[0][1]
            factor, matrix = current[1]
            current = multiply_adjacent(
                [(factor, gf2_mul(h, matrix))] + current[2:])
        elif position == len(current) - 1:
            factor, matrix = current[-2]
            h = current[-1][1]
            current = multiply_adjacent(
                current[:-2] + [(factor, gf2_mul(matrix, h))])
        else:
            factor, left = current[position - 1]
            h = current[position][1]
            right_factor, right = current[position + 1]
            if factor != right_factor:
                raise AssertionError("alternating word invariant failed")
            replacement = gf2_mul(gf2_mul(left, h), right)
            current = multiply_adjacent(
                current[:position - 1]
                + [(factor, replacement)]
                + current[position + 2:])
    return current


def amalgam_reduction_trace(word):
    """Return elementary H-absorptions certifying a trivial normal form."""
    current = multiply_adjacent(word)
    steps = []
    while len(current) > 1:
        if len(steps) > 4 * len(word):
            raise AssertionError("H-absorption trace failed to shorten")
        position = next((index for index, (_factor, matrix)
                         in enumerate(current) if lies_in_h(matrix)), None)
        if position is None:
            break
        before = record_normal_form(current)
        if position == 0:
            h = current[0][1]
            factor, matrix = current[1]
            current = multiply_adjacent(
                [(factor, gf2_mul(h, matrix))] + current[2:])
        elif position == len(current) - 1:
            factor, matrix = current[-2]
            h = current[-1][1]
            current = multiply_adjacent(
                current[:-2] + [(factor, gf2_mul(matrix, h))])
        else:
            factor, left = current[position - 1]
            h = current[position][1]
            right_factor, right = current[position + 1]
            if factor != right_factor:
                raise AssertionError("alternating word invariant failed")
            replacement = gf2_mul(gf2_mul(left, h), right)
            current = multiply_adjacent(
                current[:position - 1]
                + [(factor, replacement)]
                + current[position + 2:])
        steps.append({
            "absorbed_position": position,
            "before": before,
            "after": record_normal_form(current),
        })
    return current, steps


def transported_word(word, alignment, alignment_inverse):
    return [(factor, matrix if factor == 1 else gf2_mul(
        gf2_mul(alignment, matrix), alignment_inverse))
            for factor, matrix in word]


def record_normal_form(normal):
    return [{"factor": factor, "matrix_hex": matrix_key(matrix).hex(),
             "in_h": lies_in_h(matrix)} for factor, matrix in normal]


def run():
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    words = boundary_words()
    records = []
    all_syllables_in_h_indices = []
    lengths = Counter()
    for index, word in enumerate(words):
        transported = transported_word(word, alignment, alignment_inverse)
        if all(lies_in_h(matrix) for _factor, matrix in transported):
            all_syllables_in_h_indices.append(index)
        normal = amalgam_normal_form(transported)
        lengths[len(normal)] += 1
        if normal:
            records.append({
                "boundary_index": index,
                "free_product_length": len(word),
                "amalgam_normal_form": record_normal_form(normal),
            })
    return {
        "candidate": "A8 *_H A8",
        "alignment_hex": INNER_ALIGNMENT_HEX,
        "boundary_words": 234,
        "identity_words": 234 - len(records),
        "nonidentity_words": len(records),
        "normal_form_length_histogram": sorted(lengths.items()),
        "all_syllables_in_h_indices": all_syllables_in_h_indices,
        "all_syllables_in_h_words": len(all_syllables_in_h_indices),
        "nonidentity_records": records,
        "five_word_certificate": [{
            "boundary_index": index,
            "transported_word": record_normal_form(transported_word(
                words[index], alignment, alignment_inverse)),
            "reduction_steps": amalgam_reduction_trace(transported_word(
                words[index], alignment,
                alignment_inverse))[1],
        } for index in (0, 11, 30, 44, 55)],
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
