#!/usr/bin/env python3
"""Calibrate the simultaneous tangent geometry of the 14 shifted A4 cells.

The calculation is only 168-dimensional.  On matrix units of Reg(A8), every
adjoint left action preserves the relative coordinate x^{-1}y.  The relevant
labels generate H=GL(3,2), so each coordinate is a copy of Reg(H).  An edge
with factor-one label g1 and factor-two label g2 has translated tangent space

    Fix(g1) + Fix(R g2 R^{-1}).

This script computes the intersection of the eight distinct spaces and the
smallest positive eigenvalue of the sum of their orthogonal-complement
projections.  External multiplicity does not change either result.
"""

from collections import deque

import numpy as np

from atlas_a4_packet_generation import matrix_order, select_packet, x_lengths
from atlas_a4_rank_three_core import H18_LABEL_HEX, matrix
from atlas_a4_packet_component_audit import center, subgroup
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


REFERENCE_HEX = "00000001000100000100000000000100"


def generated_group(generators):
    moves = list(generators) + [gf2_inv(value) for value in generators]
    seen = {matrix_key(I4): I4.copy()}
    todo = deque([I4.copy()])
    while todo:
        value = todo.popleft()
        for move in moves:
            target = gf2_mul(value, move)
            key = matrix_key(target)
            if key not in seen:
                seen[key] = target
                todo.append(target)
    return seen


def cyclic_fixed_basis(elements, generator):
    """Orthonormal orbit indicators for left multiplication by generator."""
    keys = sorted(elements)
    index = {key: i for i, key in enumerate(keys)}
    permutation = []
    for key in keys:
        target = gf2_mul(generator, elements[key])
        permutation.append(index[matrix_key(target)])

    unseen = set(range(len(keys)))
    columns = []
    while unseen:
        start = min(unseen)
        orbit = []
        value = start
        while value not in orbit:
            orbit.append(value)
            unseen.discard(value)
            value = permutation[value]
        column = np.zeros(len(keys), dtype=np.float64)
        column[orbit] = 1.0 / np.sqrt(len(orbit))
        columns.append(column)
    return np.column_stack(columns)


def range_projection(columns, tolerance=1e-10):
    left, singular_values, _right = np.linalg.svd(columns, full_matrices=False)
    rank = int(np.sum(singular_values > tolerance))
    basis = left[:, :rank]
    return basis @ basis.T, rank


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())

    h18 = subgroup([matrix(value) for value in H18_LABEL_HEX])
    central_order_three = {
        matrix_key(value)
        for value in center(h18)
        if matrix_key(value) != matrix_key(I4)
    }
    reference = matrix(REFERENCE_HEX)
    reference_inverse = gf2_inv(reference)

    pairs = {}
    generators = []
    for _tree_index, word in packet:
        by_factor = {factor: value for factor, value in word}
        order_three = next(
            value for value in by_factor.values() if matrix_order(value) == 3
        )
        if matrix_key(order_three) in central_order_three:
            continue
        left = by_factor[1]
        right = gf2_mul(gf2_mul(reference, by_factor[2]), reference_inverse)
        pair_key = (matrix_key(left), matrix_key(right))
        pairs[pair_key] = (left, right)
        generators.extend((left, right))

    if len(pairs) != 8:
        raise AssertionError(f"expected eight distinct core pairs, got {len(pairs)}")
    group = generated_group(generators)
    if len(group) != 168:
        raise AssertionError(f"translated core generated {len(group)}, not 168")

    identity = np.eye(168)
    laplacian = np.zeros((168, 168), dtype=np.float64)
    sum_dimensions = []
    for left, right in pairs.values():
        left_basis = cyclic_fixed_basis(group, left)
        right_basis = cyclic_fixed_basis(group, right)
        projection, rank = range_projection(np.column_stack((left_basis, right_basis)))
        sum_dimensions.append(rank)
        laplacian += identity - projection

    eigenvalues = np.linalg.eigvalsh((laplacian + laplacian.T) / 2.0)
    zero_count = int(np.sum(np.abs(eigenvalues) < 1e-9))
    positive = eigenvalues[eigenvalues >= 1e-9]
    print("distinct translated core pairs:", len(pairs))
    print("generated subgroup order:", len(group))
    print("edge tangent-sum dimensions:", sorted(sum_dimensions))
    print("common tangent dimension:", zero_count)
    print("smallest 20 eigenvalues:")
    print(" ".join(f"{value:.15g}" for value in eigenvalues[:20]))
    if positive.size:
        print("smallest positive tangent Laplacian eigenvalue:", f"{positive[0]:.15g}")


if __name__ == "__main__":
    main()
