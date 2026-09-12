"""Rationalize and exactly verify an SL(3,Z) group-ring SOS candidate.

If Q is a rational matrix, Q^T Q is positive semidefinite exactly.  This
program interprets its indices as (generator, group-support) pairs, computes
the resulting matrix-group-ring Gram element with Python integers, and
compares it coefficientwise with Delta-cI.  For the self-adjoint residual R,

    ||pi(R)|| <= max_i sum_(j,g) |R_ij(g)|

in every unitary representation.  Consequently a positive value of

    c - max_i sum_(j,g) |R_ij(g)|

is a rigorous universal Hodge lower bound.  The saved NPZ contains the
integer numerator matrix and scalar denominator; verification does not use
the original floating-point Gram matrix.
"""

import argparse
import json
import math

import numpy as np

from sl3_group_ring_sos import (
    IDENTITY,
    ROOTS,
    coefficient_pairs,
    expanded_support,
    hodge_matrix,
    matrix_inverse,
)


def rational_factor(gram_path, denominator, eigen_cutoff):
    gram = np.load(gram_path)
    gram = 0.5 * (gram + gram.T)
    eigenvalues, eigenvectors = np.linalg.eigh(gram)
    keep = eigenvalues > eigen_cutoff
    factor = (np.sqrt(eigenvalues[keep])[:, None] *
              eigenvectors[:, keep].T)
    numerators = np.rint(factor * denominator).astype(np.int64).astype(object)
    return numerators, eigenvalues, int(np.sum(keep))


def gram_coefficients(factor_numerators, support):
    gram_numerators = factor_numerators.T @ factor_numerators
    pairs = coefficient_pairs(support)
    block_size = len(support)
    answer = [[{} for _ in ROOTS] for _ in ROOTS]
    for left in range(len(ROOTS)):
        left_offset = left * block_size
        for right in range(len(ROOTS)):
            right_offset = right * block_size
            entry = {}
            for group, locations in pairs.items():
                coefficient = sum(
                    gram_numerators[left_offset + source,
                                    right_offset + target]
                    for source, target in locations)
                if coefficient:
                    entry[group] = int(coefficient)
            answer[left][right] = entry
    return answer


def exact_residual(factor_numerators, denominator, radius,
                   gap_numerator, gap_denominator):
    (_names, generator_matrices, _d0, _d1, delta,
     prefix_support) = hodge_matrix()
    support = expanded_support(prefix_support, generator_matrices, radius)
    expected_dimension = len(ROOTS) * len(support)
    if factor_numerators.shape[1] != expected_dimension:
        raise ValueError("factor has %d columns; expected %d" %
                         (factor_numerators.shape[1], expected_dimension))
    gram = gram_coefficients(factor_numerators, support)

    square_denominator = denominator * denominator
    common_denominator = math.lcm(square_denominator, gap_denominator)
    gram_scale = common_denominator // square_denominator
    gap_scale = common_denominator // gap_denominator
    row_bounds = []
    residual_terms = 0
    residual_max_coefficient = 0
    hermitian_residual = [[{} for _ in ROOTS] for _ in ROOTS]
    for left in range(len(ROOTS)):
        row_bound = 0
        for right in range(len(ROOTS)):
            groups = set(delta[left][right]) | set(gram[left][right])
            if left == right:
                groups.add(IDENTITY)
            entry = {}
            for group in groups:
                numerator = (delta[left][right].get(group, 0) *
                             common_denominator)
                if left == right and group == IDENTITY:
                    numerator -= gap_numerator * gap_scale
                numerator -= gram[left][right].get(group, 0) * gram_scale
                if numerator:
                    entry[group] = numerator
                    absolute = abs(numerator)
                    row_bound += absolute
                    residual_terms += 1
                    residual_max_coefficient = max(
                        residual_max_coefficient, absolute)
            hermitian_residual[left][right] = entry
        row_bounds.append(row_bound)

    for left in range(len(ROOTS)):
        for right in range(len(ROOTS)):
            # Spell out the adjoint check without rational arithmetic: the
            # common denominator is shared by every coefficient.
            adjoint = {
                matrix_inverse(group): value
                for group, value in hermitian_residual[right][left].items()
            }
            if hermitian_residual[left][right] != adjoint:
                raise AssertionError("residual is not self-adjoint")

    residual_bound_numerator = max(row_bounds)
    gap_at_common_scale = gap_numerator * gap_scale
    certified_numerator = gap_at_common_scale - residual_bound_numerator
    return {
        "radius": radius,
        "support": len(support),
        "factor_rows": int(factor_numerators.shape[0]),
        "factor_columns": int(factor_numerators.shape[1]),
        "factor_denominator": denominator,
        "gap_numerator": gap_numerator,
        "gap_denominator": gap_denominator,
        "common_denominator": common_denominator,
        "residual_terms": residual_terms,
        "residual_max_coefficient_numerator": residual_max_coefficient,
        "row_bound_numerators": row_bounds,
        "residual_bound_numerator": residual_bound_numerator,
        "residual_bound": residual_bound_numerator / common_denominator,
        "certified_gap_numerator": certified_numerator,
        "certified_gap": certified_numerator / common_denominator,
        "valid": certified_numerator > 0,
    }


def save_certificate(path, factor_numerators, denominator, radius,
                     gap_numerator, gap_denominator):
    # Values exceed int64 after Gram multiplication, but the rounded factor
    # itself is kept within int64 in the intended runs.  Reject rather than
    # silently wrap if a larger denominator is requested.
    maximum = max(abs(int(value)) for value in factor_numerators.flat)
    if maximum > np.iinfo(np.int64).max:
        raise OverflowError("factor numerator exceeds int64")
    (_names, generator_matrices, _d0, _d1, _delta,
     prefix_support) = hodge_matrix()
    support = expanded_support(prefix_support, generator_matrices, radius)
    np.savez_compressed(
        path,
        factor_numerators=np.asarray(factor_numerators, dtype=np.int64),
        group_support=np.asarray(support, dtype=np.int64),
        factor_denominator=np.asarray([denominator], dtype=np.int64),
        radius=np.asarray([radius], dtype=np.int64),
        gap_numerator=np.asarray([gap_numerator], dtype=np.int64),
        gap_denominator=np.asarray([gap_denominator], dtype=np.int64),
    )


def load_certificate(path):
    archive = np.load(path)
    return (
        archive["factor_numerators"].astype(object),
        int(archive["factor_denominator"][0]),
        int(archive["radius"][0]),
        int(archive["gap_numerator"][0]),
        int(archive["gap_denominator"][0]),
        archive["group_support"].astype(np.int64),
    )


def check_stored_support(radius, stored_support):
    (_names, generator_matrices, _d0, _d1, _delta,
     prefix_support) = hodge_matrix()
    expected = np.asarray(
        expanded_support(prefix_support, generator_matrices, radius),
        dtype=np.int64)
    if not np.array_equal(stored_support, expected):
        raise AssertionError("certificate group support does not match source")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gram")
    parser.add_argument("--certificate", required=True)
    parser.add_argument("--denominator", type=int, default=100000000)
    parser.add_argument("--eigen-cutoff", type=float, default=0.0)
    parser.add_argument("--radius", type=int, default=0)
    parser.add_argument("--gap-numerator", type=int, default=1)
    parser.add_argument("--gap-denominator", type=int, default=250)
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()

    if args.verify:
        (factor, denominator, radius, gap_numerator, gap_denominator,
         stored_support) = (
            load_certificate(args.certificate))
        check_stored_support(radius, stored_support)
        result = exact_residual(factor, denominator, radius,
                                gap_numerator, gap_denominator)
        print(json.dumps(result))
        return

    if not args.gram:
        parser.error("--gram is required unless --verify is used")
    factor, eigenvalues, rank = rational_factor(
        args.gram, args.denominator, args.eigen_cutoff)
    save_certificate(args.certificate, factor, args.denominator, args.radius,
                     args.gap_numerator, args.gap_denominator)
    result = exact_residual(factor, args.denominator, args.radius,
                            args.gap_numerator, args.gap_denominator)
    result.update({
        "numerical_gram_min_eigenvalue": float(eigenvalues[0]),
        "numerical_gram_max_eigenvalue": float(eigenvalues[-1]),
        "retained_numerical_rank": rank,
    })
    print(json.dumps(result))


if __name__ == "__main__":
    main()
