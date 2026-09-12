"""Search finite ``A8`` images of the five-word rank-three quotient.

After transporting the second chart through the certified alignment ``k0``,
the five selected collision words lie in ``H_1 * H_2`` with

    H = diag(GL(3,2), 1) < GL(4,2) ~= A8.

For every ``c in A8`` this script evaluates the homomorphism

    H_1 * H_2 -> A8,
    h_1 |-> h,
    h_2 |-> c h c^-1.

A solution outside the normalizer of ``H`` is an explicit finite quotient
of the five-relator group in which the two copies of ``H`` are distinct.
That certifies a genuinely nonlinear residue which cannot be seen by the
full-rank rational tangent calculation.
"""

import json

import numpy as np

from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


INDICES = (0, 11, 30, 44, 55)
H_GENERATORS = ((0, 1), (1, 0), (1, 2), (2, 1))


def transvection(row, column):
    value = I4.copy()
    value[row, column] ^= 1
    return value


def transported_word(word, alignment, alignment_inverse):
    output = []
    for factor, value in word:
        image = value if factor == 1 else gf2_mul(
            gf2_mul(alignment, value), alignment_inverse)
        expected = I4.copy()
        expected[:3, :3] = image[:3, :3]
        if not np.array_equal(image, expected):
            raise AssertionError("five-word packet escaped H")
        output.append((factor, image))
    return output


def evaluate(word, conjugator, conjugator_inverse):
    value = I4.copy()
    for factor, letter in word:
        image = letter if factor == 1 else gf2_mul(
            gf2_mul(conjugator, letter), conjugator_inverse)
        value = gf2_mul(value, image)
    return value


def generated_group(generators):
    elements = [I4.copy()]
    seen = {matrix_key(I4)}
    for value in elements:
        for generator in generators:
            target = gf2_mul(value, generator)
            key = matrix_key(target)
            if key not in seen:
                seen.add(key)
                elements.append(target)
    return elements


def main():
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    selected = [transported_word(boundary_words()[index], alignment,
                                 alignment_inverse)
                for index in INDICES]
    h_generators = [transvection(*position) for position in H_GENERATORS]

    solutions = []
    for conjugator in enumerate_gl4():
        conjugator_inverse = gf2_inv(conjugator)
        if not all(np.array_equal(
                evaluate(word, conjugator, conjugator_inverse), I4)
                   for word in selected):
            continue
        second_generators = [gf2_mul(
            gf2_mul(conjugator, generator), conjugator_inverse)
                             for generator in h_generators]
        bridges = [gf2_mul(second, gf2_inv(first))
                   for first, second in zip(h_generators,
                                            second_generators)]
        image = generated_group(h_generators + second_generators)
        solutions.append({
            "conjugator_hex": matrix_key(conjugator).hex(),
            "copies_equal": all(np.array_equal(bridge, I4)
                                for bridge in bridges),
            "bridge_hex": [matrix_key(bridge).hex() for bridge in bridges],
            "image_order": len(image),
        })

    unequal = [record for record in solutions if not record["copies_equal"]]
    print(json.dumps({
        "ambient": "GL(4,2) ~= A8",
        "h_order": len(generated_group(h_generators)),
        "relator_indices": list(INDICES),
        "conjugators_tested": 20160,
        "solutions": len(solutions),
        "unequal_copy_solutions": len(unequal),
        "image_order_histogram": {
            str(order): sum(record["image_order"] == order
                            for record in solutions)
            for order in sorted({record["image_order"]
                                 for record in solutions})
        },
        "unequal_copy_certificates": unequal,
    }, indent=2))


if __name__ == "__main__":
    main()
