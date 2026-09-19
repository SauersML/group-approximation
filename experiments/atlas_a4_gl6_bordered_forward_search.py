#!/usr/bin/env python3
"""Search exact one-coordinate GL6 lifts for one forward central-C3 edge.

For each certified GL5 relative frame, keep its upper-left 5-by-5 block and
exhaust the 2^11 choices of a last column, last row, and bottom-right entry.
Every invertible border is tested against the fourteen core pair-cubes,
collision 19243, and one representative of the forward directed central
K2,2 block.  This is a bounded exact F2 screen intended for MSI.
"""

import argparse
import itertools
import json

import numpy as np

from atlas_a4_gl5_core_collision_countermodel import CERTIFICATES, CENTRAL_C3_HEX
from atlas_a4_parabolic_completion import core_and_collision
from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words


I6 = np.eye(6, dtype=np.uint8)


def embed4(matrix):
    out = I6.copy()
    out[:4, :4] = matrix
    return out


def multiply(left, right):
    return (left @ right) & 1


def inverse(matrix):
    augmented = np.concatenate((matrix.copy(), I6.copy()), axis=1)
    for column in range(6):
        pivot = next(
            (row for row in range(column, 6) if augmented[row, column]),
            None,
        )
        if pivot is None:
            return None
        augmented[[column, pivot]] = augmented[[pivot, column]]
        for row in range(6):
            if row != column and augmented[row, column]:
                augmented[row] ^= augmented[column]
    return augmented[:, 6:]


def word_value(word, relative, relative_inverse):
    value = I6.copy()
    for factor, matrix in word:
        image = embed4(matrix)
        if factor == 2:
            image = multiply(multiply(relative, image), relative_inverse)
        value = multiply(value, image)
    return value


def cube_holds(word, relative, relative_inverse):
    value = word_value(word, relative, relative_inverse)
    return np.array_equal(multiply(multiply(value, value), value), I6)


def forward_representative(full_packet):
    for word in full_packet:
        by_factor = {factor: matrix for factor, matrix in word}
        first_hex = bytes(by_factor[1].reshape(-1)).hex()
        second_hex = bytes(by_factor[2].reshape(-1)).hex()
        if first_hex in CENTRAL_C3_HEX and second_hex not in CENTRAL_C3_HEX:
            return word, first_hex, second_hex
    raise AssertionError("forward central-C3 representative disappeared")


def bordered_matrices(base):
    for bits in itertools.product((0, 1), repeat=11):
        relative = np.zeros((6, 6), dtype=np.uint8)
        relative[:5, :5] = base
        relative[:5, 5] = bits[:5]
        relative[5, :5] = bits[5:10]
        relative[5, 5] = bits[10]
        yield bits, relative


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--base",
        choices=("core14", "reverse22", "both"),
        default="both",
    )
    args = parser.parse_args()

    core, collision = core_and_collision()
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    full_packet = [word for _index, word in select_packet(words, x_lengths())]
    forward, first_hex, second_hex = forward_representative(full_packet)

    names = tuple(CERTIFICATES) if args.base == "both" else (args.base,)
    output = {
        "forward_representative_first_hex": first_hex,
        "forward_representative_second_hex": second_hex,
        "bases": {},
    }
    for name in names:
        base = np.frombuffer(
            bytes.fromhex(CERTIFICATES[name]["relative_hex"]), dtype=np.uint8
        ).reshape(5, 5)
        invertible_borders = 0
        survivor = None
        for bits, relative in bordered_matrices(base):
            relative_inverse = inverse(relative)
            if relative_inverse is None:
                continue
            invertible_borders += 1
            if not all(cube_holds(word, relative, relative_inverse) for word in core):
                continue
            if not np.array_equal(word_value(collision, relative, relative_inverse), I6):
                continue
            if not cube_holds(forward, relative, relative_inverse):
                continue
            survivor = {
                "border_bits": "".join(map(str, bits)),
                "relative_matrix_hex": bytes(relative.reshape(-1)).hex(),
            }
            break
        output["bases"][name] = {
            "invertible_borders_tested": invertible_borders,
            "survivor": survivor,
        }

    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
