"""Test the five-row Atlas phase lift in the universal affine F2 model.

The proposed phase inequality uses boundary rows 0, 11, 30, 44, 55 and
the interior commutator c_19243.  At the certified inner fold all six words
are trivial.  Their right-trivialized derivatives therefore generate a left
ideal I in F2[A8].  For M=F2[A8]/I and m=1+I, the standard affine chart

    beta(g)=((1+g)m,g)

kills all six nonlinear words exactly.  If one of the four H-bridges 1+h is
not in I, the resulting finite affine model retains positive H covariance;
the established five-row tangent coercivity then forces positive five-row
linear energy and refutes the proposed nonlinear-to-linear inequality.

This script performs only exact bit arithmetic and emits bridge-membership
and dual-certificate data.  It must be run remotely on MSI, not locally.
"""

import argparse
from collections import deque
import json
import time

from atlas_asc_packet_build import interior_word
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_certified_a8_alignment import boundary_words
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_two_chart_search import I4, factor_generators, gf2_inv, gf2_mul, matrix_key
from atlas_universal_modular_group_algebra import (
    LeftTranslations,
    aligned_derivative,
    insert_row,
    population_count,
    reduce_row,
)


SELECTED = (0, 11, 30, 44, 55)


def parity(value):
    """Parity of an integer bitset, compatible with MSI's Python 3.6."""
    return bin(value).count("1") & 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-seconds", type=float, default=120.0)
    parser.add_argument("--report-every", type=int, default=250)
    args = parser.parse_args()
    started = time.monotonic()

    elements = list(enumerate_gl4())
    index_by_key = {
        matrix_key(element): index for index, element in enumerate(elements)
    }
    source_generators = [
        word[0][1] for _name, word in factor_generators()[:6]
    ]
    permutations = [
        [index_by_key[matrix_key(gf2_mul(generator, element))]
         for element in elements]
        for generator in source_generators
    ]
    translations = LeftTranslations(permutations, len(elements))
    alignment = next(
        element for element in elements
        if matrix_key(element).hex() == INNER_ALIGNMENT_HEX
    )
    alignment_inverse = gf2_inv(alignment)

    boundary = boundary_words()
    selected_words = [boundary[index] for index in SELECTED]
    interior, _q = interior_word(alignment, alignment_inverse)
    seeds = [
        aligned_derivative(word, alignment, alignment_inverse, index_by_key)
        for word in selected_words
    ]
    # ``interior_word`` is already transported through the certified
    # alignment, so its fold derivative is taken at the identity frame.
    seeds.append(aligned_derivative(interior, I4, I4, index_by_key))

    h_targets = []
    for row, column in ((0, 1), (1, 0), (1, 2), (2, 1)):
        h = I4.copy()
        h[row, column] ^= 1
        h_targets.append(
            (1 << index_by_key[matrix_key(I4)])
            ^ (1 << index_by_key[matrix_key(h)])
        )

    basis = {}
    basis_rows = []
    queue = deque()
    for seed in seeds:
        residual, _reductions = insert_row(basis, seed)
        if residual:
            row_id = len(basis_rows)
            basis[residual.bit_length() - 1] = (residual, row_id)
            basis_rows.append(residual)
            queue.append(row_id)

    def target_remainders():
        return [reduce_row(basis, target)[0] for target in h_targets]

    remainders = target_remainders()
    processed = 0
    timed_out = False
    while queue:
        if time.monotonic() - started > args.max_seconds:
            timed_out = True
            break
        parent_id = queue.popleft()
        for image in translations.all_images(basis_rows[parent_id]):
            processed += 1
            residual, _reductions = insert_row(basis, image)
            if residual:
                row_id = len(basis_rows)
                basis[residual.bit_length() - 1] = (residual, row_id)
                basis_rows.append(residual)
                queue.append(row_id)
                remainders = target_remainders()
        if len(basis) and len(basis) % args.report_every == 0:
            print(json.dumps({
                "rank": len(basis),
                "queue": len(queue),
                "target_weights": [population_count(value)
                                   for value in remainders],
                "elapsed_seconds": round(time.monotonic() - started, 3),
            }), flush=True)

    remainders = target_remainders()

    def dual_witness(target, remainder):
        if not remainder:
            return None
        free_bit = remainder & -remainder
        functional = free_bit
        for pivot in sorted(basis):
            row, _row_id = basis[pivot]
            if parity(row & functional):
                functional ^= 1 << pivot
        if any(parity(row & functional)
               for row, _row_id in basis.values()):
            raise AssertionError("dual witness does not annihilate ideal")
        if not parity(target & functional):
            raise AssertionError("dual witness does not detect bridge")
        return [index for index in range(len(elements))
                if (functional >> index) & 1]

    witnesses = [
        dual_witness(target, remainder)
        for target, remainder in zip(h_targets, remainders)
    ]
    print(json.dumps({
        "field": "F2",
        "group": "A8",
        "selected_boundary_indices": list(SELECTED),
        "interior_word_included": True,
        "seed_count": len(seeds),
        "left_ideal_rank": len(basis),
        "quotient_dimension": len(elements) - len(basis),
        "queue_remaining": len(queue),
        "translations_processed": processed,
        "h_bridge_remainder_weights": [population_count(value)
                                       for value in remainders],
        "all_h_bridges_in_ideal": not any(remainders),
        "dual_witness_support_sizes": [
            None if witness is None else len(witness)
            for witness in witnesses
        ],
        "dual_witness_supports": witnesses,
        "timed_out": timed_out,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }, indent=2))


if __name__ == "__main__":
    main()
