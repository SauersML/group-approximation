"""Test the full boundary against the hidden two-primary H bridges.

The five-word rational tangent certificate leaves ``(C2)^8`` in the exact
Schreier abelianization of the rank-three fold kernel.  The other 229 words,
especially the 24 that leave ``H*H``, may kill this torsion.  In the universal
``F2[A8]`` relation module this is the membership question

    1 + h in < d_q : q is one of all 234 boundary words >_left

for four transvections generating H.  The script closes the sparse seed row
space under the six A8 left translations and stops as soon as all bridges
are present.
"""

import argparse
from collections import deque
import json
import time

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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-seconds", type=float, default=120.0)
    parser.add_argument("--report-every", type=int, default=250)
    args = parser.parse_args()
    started = time.monotonic()

    elements = list(enumerate_gl4())
    index_by_key = {matrix_key(element): index
                    for index, element in enumerate(elements)}
    source_generators = [
        word[0][1] for _name, word in factor_generators()[:6]
    ]
    permutations = [[index_by_key[matrix_key(gf2_mul(generator, element))]
                     for element in elements]
                    for generator in source_generators]
    translations = LeftTranslations(permutations, len(elements))
    alignment = next(element for element in elements
                     if matrix_key(element).hex() == INNER_ALIGNMENT_HEX)
    alignment_inverse = gf2_inv(alignment)
    seeds = [aligned_derivative(
        word, alignment, alignment_inverse, index_by_key)
             for word in boundary_words()]

    h_targets = []
    for row, column in ((0, 1), (1, 0), (1, 2), (2, 1)):
        h = I4.copy()
        h[row, column] ^= 1
        h_targets.append(
            (1 << index_by_key[matrix_key(I4)])
            ^ (1 << index_by_key[matrix_key(h)]))

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
    while any(remainders) and queue:
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
                if not any(remainders):
                    break
        if len(basis) and len(basis) % args.report_every == 0:
            print(json.dumps({
                "rank": len(basis),
                "queue": len(queue),
                "target_weights": [population_count(value)
                                   for value in remainders],
                "elapsed_seconds": round(time.monotonic() - started, 3),
            }), flush=True)

    def dual_witness(target, remainder):
        if not remainder:
            return None
        free_bit = remainder & -remainder
        functional = free_bit
        for pivot in sorted(basis):
            row, _row_id = basis[pivot]
            if (row & functional).bit_count() & 1:
                functional ^= 1 << pivot
        if any((row & functional).bit_count() & 1
               for row, _row_id in basis.values()):
            raise AssertionError("dual witness does not annihilate ideal")
        if not ((target & functional).bit_count() & 1):
            raise AssertionError("dual witness does not detect bridge")
        return [index for index in range(len(elements))
                if (functional >> index) & 1]

    witnesses = [dual_witness(target, remainder)
                 for target, remainder in zip(h_targets, remainders)]

    print(json.dumps({
        "field": "F2",
        "group": "A8",
        "boundary_seeds": len(seeds),
        "left_ideal_rank": len(basis),
        "queue_remaining": len(queue),
        "translations_processed": processed,
        "h_bridge_remainder_weights": [population_count(value)
                                       for value in remainders],
        "all_h_bridges_in_boundary_ideal": not any(remainders),
        "dual_witness_supports": witnesses,
        "dual_witness_support_sizes": [
            None if witness is None else len(witness)
            for witness in witnesses],
        "timed_out": timed_out,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }, indent=2))


if __name__ == "__main__":
    main()
