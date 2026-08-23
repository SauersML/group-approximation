#!/usr/bin/env python3
"""Exact finite screens for the five-row operator-phase lift.

This is deliberately a bounded finite-model audit.  It checks the stored
GL8(2) multiplicity-two frame, the two stored collision-zero GL5(2) frames,
and every inner relative frame in A8.  It does not certify the uniform
amplified inequality.
"""

import json
from collections import Counter

import numpy as np

from atlas_a4_gl5_core_collision_countermodel import CERTIFICATES
from atlas_a4_gl5_packet_screen import I5, embed4, inv5, key5, mul5
from atlas_asc_inner_link_scan import conjugate, prefixes
from atlas_asc_packet_build import interior_word, merge
from atlas_boundary_amalgam_normal_form import transported_word
from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


INDICES = (0, 11, 30, 44, 55)
GL8_ESCAPE = int("401004080301c030", 16)
MULTIPLICATION_BLOCKS = ((0, 0), (1, 2), (2, 3), (3, 1))


def multiply(left, right):
    return (left @ right) & 1


def inverse(value):
    size = value.shape[0]
    augmented = np.concatenate(
        (value.copy(), np.eye(size, dtype=np.uint8)), axis=1
    )
    for column in range(size):
        pivot = next(
            row for row in range(column, size) if augmented[row, column]
        )
        augmented[[column, pivot]] = augmented[[pivot, column]]
        for row in range(size):
            if row != column and augmented[row, column]:
                augmented[row] ^= augmented[column]
    return augmented[:, size:]


def rank(value):
    value = value.copy()
    pivot_row = 0
    for column in range(value.shape[1]):
        pivots = np.flatnonzero(value[pivot_row:, column])
        if not len(pivots):
            continue
        pivot = pivot_row + int(pivots[0])
        value[[pivot_row, pivot]] = value[[pivot, pivot_row]]
        for row in range(value.shape[0]):
            if row != pivot_row and value[row, column]:
                value[row] ^= value[pivot_row]
        pivot_row += 1
    return pivot_row


def repeated_natural(value):
    output = np.zeros((8, 8), dtype=np.uint8)
    for row in range(4):
        for column in range(4):
            first, second = MULTIPLICATION_BLOCKS[int(value[row, column])]
            output[2 * row, 2 * column] = first & 1
            output[2 * row, 2 * column + 1] = first >> 1
            output[2 * row + 1, 2 * column] = second & 1
            output[2 * row + 1, 2 * column + 1] = second >> 1
    return output


def matrix8(value):
    return np.array(
        [[(value >> (8 * row + column)) & 1 for column in range(8)]
         for row in range(8)],
        dtype=np.uint8,
    )


def evaluate(word, relative, relative_inverse, identity, lift, mul):
    value = identity.copy()
    for factor, letter in word:
        image = lift(letter)
        if factor == 2:
            image = mul(mul(relative, image), relative_inverse)
        value = mul(value, image)
    return value


def gl8_screen(raw_words, aligned_words, alignment):
    frame = matrix8(GL8_ESCAPE)
    frame_inverse = inverse(frame)
    identity = np.eye(8, dtype=np.uint8)
    values = [evaluate(
        raw_words[index], frame_inverse, frame, identity,
        repeated_natural, multiply,
    ) for index in INDICES]

    # In aligned coordinates the canonical relative frame is F^-1 A^-1.
    relative = multiply(frame_inverse, inverse(repeated_natural(alignment)))
    energies = []
    supports = []
    for word in aligned_words:
        pairs, fold = prefixes(word)
        assert np.array_equal(fold, I4)
        coefficients = Counter()
        for before, after in pairs:
            for coefficient, prefix in ((1, before), (-1, after)):
                lifted = repeated_natural(prefix)
                image = multiply(multiply(lifted, relative), inverse(lifted))
                coefficients[bytes(image.reshape(-1))] += coefficient
        energies.append(sum(value * value for value in coefficients.values()))
        supports.append(sum(value != 0 for value in coefficients.values()))

    ranks = [rank(value ^ identity) for value in values]
    assert ranks == [2, 2, 2, 2, 2]
    assert energies == [6, 8, 8, 8, 8]
    assert supports == energies
    return {
        "relative_frame_hex": f"{GL8_ESCAPE:016x}",
        "collision_19243": "identity",
        "interior_commutator": "identity",
        "five_boundary_identity": [False] * 5,
        "five_boundary_rank_of_value_minus_identity": ranks,
        "regular_linear_energy_by_row": energies,
        "regular_linear_energy_total": sum(energies),
        "regular_nonlinear_energy_total": 10,
        "energy_ratio": "19/5",
    }


def gl5_screen(raw_words):
    records = {}
    for name, certificate in CERTIFICATES.items():
        relative = np.frombuffer(
            bytes.fromhex(certificate["relative_hex"]), dtype=np.uint8
        ).reshape(5, 5)
        relative_inverse = inv5(relative)
        identities = [np.array_equal(evaluate(
            raw_words[index], relative, relative_inverse, I5, embed4, mul5
        ), I5) for index in INDICES]
        records[name] = {
            "relative_frame_hex": key5(relative).hex(),
            "collision_19243": "identity",
            "interior_commutator": "identity",
            "five_boundary_identity": identities,
        }
    assert records["core14"]["five_boundary_identity"] == [False] * 5
    assert records["reverse22"]["five_boundary_identity"] == [
        True, False, False, False, False
    ]
    return records


def inner_a8_screen(aligned_words, interior):
    solutions = []
    for relative in enumerate_gl4():
        relative_inverse = gf2_inv(relative)
        values = [evaluate(
            word, relative, relative_inverse, I4,
            lambda value: value, gf2_mul,
        ) for word in aligned_words]
        if not all(np.array_equal(value, I4) for value in values):
            continue
        linear_energies = []
        for word in aligned_words:
            pairs, _fold = prefixes(word)
            coefficients = Counter()
            for before, after in pairs:
                coefficients[matrix_key(conjugate(before, relative))] += 1
                coefficients[matrix_key(conjugate(after, relative))] -= 1
            linear_energies.append(sum(
                value * value for value in coefficients.values()
            ))
        interior_identity = np.array_equal(evaluate(
            interior, relative, relative_inverse, I4,
            lambda value: value, gf2_mul,
        ), I4)
        solutions.append({
            "relative_frame_hex": matrix_key(relative).hex(),
            "interior_identity": bool(interior_identity),
            "linear_energies": linear_energies,
        })
    assert solutions == [{
        "relative_frame_hex": matrix_key(I4).hex(),
        "interior_identity": False,
        "linear_energies": [0, 0, 0, 0, 0],
    }]
    return {
        "relative_frames_tested": 20160,
        "five_boundary_solutions": len(solutions),
        "five_plus_interior_solutions": sum(
            record["interior_identity"] for record in solutions
        ),
        "solutions": solutions,
    }


def main():
    raw_words = boundary_words()
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    aligned_words = [merge(transported_word(
        raw_words[index], alignment, alignment_inverse
    )) for index in INDICES]
    interior, _collision = interior_word(alignment, alignment_inverse)
    output = {
        "indices": list(INDICES),
        "phase_edge_counts": [len(prefixes(word)[0]) for word in aligned_words],
        "boundary_phase_edges": sum(
            len(prefixes(word)[0]) for word in aligned_words
        ),
        "interior_phase_edges": sum(factor == 2 for factor, _ in interior),
        "gl8_multiplicity_two": gl8_screen(
            raw_words, aligned_words, alignment
        ),
        "gl5_collision_zero_frames": gl5_screen(raw_words),
        "inner_a8_exhaustion": inner_a8_screen(aligned_words, interior),
        "scope": "finite exact evidence only; no uniform amplified gap",
    }
    assert output["phase_edge_counts"] == [3, 4, 4, 4, 4]
    assert output["boundary_phase_edges"] == 19
    assert output["interior_phase_edges"] == 8
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
