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

from collections import Counter, deque

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


def left_coset_blocks(group, subgroup):
    """Index blocks for the left-subgroup orbits in the regular action."""
    group_keys = sorted(group)
    index = {key: i for i, key in enumerate(group_keys)}
    subgroup_values = [subgroup[key] for key in sorted(subgroup)]
    unseen = set(group_keys)
    blocks = []
    while unseen:
        representative_key = min(unseen)
        representative = group[representative_key]
        orbit_keys = [
            matrix_key(gf2_mul(value, representative))
            for value in subgroup_values
        ]
        blocks.append([index[key] for key in orbit_keys])
        unseen.difference_update(orbit_keys)
    return np.asarray(blocks, dtype=np.int64), subgroup_values


def local_sum_projection(subgroup_values, left, right):
    """Projection onto Fix(left)+Fix(right) in one regular subgroup block."""
    elements = {matrix_key(value): value for value in subgroup_values}
    left_basis = cyclic_fixed_basis(elements, left)
    right_basis = cyclic_fixed_basis(elements, right)
    return range_projection(np.column_stack((left_basis, right_basis)))


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
    if len(group) not in (168, 20160):
        raise AssertionError(f"unexpected translated core group order {len(group)}")

    pair_values = list(pairs.values())
    edge_operators = []
    sum_dimensions = []
    local_group_orders = []
    for left, right in pair_values:
        local_group = generated_group((left, right))
        local_group_orders.append(len(local_group))
        blocks, local_values = left_coset_blocks(group, local_group)
        local_projection, local_rank = local_sum_projection(local_values, left, right)
        edge_operators.append((blocks, local_projection))
        sum_dimensions.append(local_rank * blocks.shape[0])

    dimension = len(group)

    # A choice of one endpoint from every tangent sum gives an exact common
    # subspace: vectors fixed by the subgroup generated by those endpoints.
    choice_orders = Counter()
    smallest_choice = None
    for mask in range(1 << len(pair_values)):
        selected = [
            pair[1 if (mask >> index) & 1 else 0]
            for index, pair in enumerate(pair_values)
        ]
        selected_group = generated_group(selected)
        order = len(selected_group)
        choice_orders[order] += 1
        record = (order, mask, selected)
        if smallest_choice is None or record[:2] < smallest_choice[:2]:
            smallest_choice = record

    def apply_projection(vector, edge_operator):
        blocks, local_projection = edge_operator
        output = np.zeros_like(vector)
        if vector.ndim == 1:
            output[blocks] = vector[blocks] @ local_projection.T
        else:
            block_values = vector[blocks, :]
            output[blocks, :] = np.einsum(
                "ij,bjk->bik", local_projection, block_values
            )
        return output

    def apply_laplacian(vector):
        output = np.zeros_like(vector)
        for edge_operator in edge_operators:
            output += vector - apply_projection(vector, edge_operator)
        return output

    # Alternating projections expose the dimension of the common fixed space.
    rng = np.random.default_rng(19243)
    samples = rng.normal(size=(dimension, 24))
    samples -= np.mean(samples, axis=0, keepdims=True)
    initial_norm = np.linalg.norm(samples)
    decay = []
    for sweep in range(800):
        for edge_operator in edge_operators:
            samples = apply_projection(samples, edge_operator)
        if sweep + 1 in (50, 200, 800):
            decay.append((sweep + 1, np.linalg.norm(samples) / initial_norm))
    singular_values = np.linalg.svd(samples / initial_norm, compute_uv=False)

    # A fully reorthogonalized scalar Lanczos calibration gives the bottom of
    # the tangent Laplacian spectrum without forming a 20160-square matrix.
    lanczos_steps = 220
    vector = rng.normal(size=dimension)
    vector /= np.linalg.norm(vector)
    basis = np.zeros((dimension, lanczos_steps), dtype=np.float64)
    alphas = np.zeros(lanczos_steps, dtype=np.float64)
    betas = np.zeros(lanczos_steps - 1, dtype=np.float64)
    previous = np.zeros(dimension, dtype=np.float64)
    completed = lanczos_steps
    for step in range(lanczos_steps):
        basis[:, step] = vector
        target = apply_laplacian(vector)
        if step:
            target -= betas[step - 1] * previous
        alphas[step] = np.dot(vector, target)
        target -= alphas[step] * vector
        # Two passes keep the small Ritz values reliable.
        for _pass in range(2):
            target -= basis[:, : step + 1] @ (basis[:, : step + 1].T @ target)
        if step == lanczos_steps - 1:
            break
        betas[step] = np.linalg.norm(target)
        if betas[step] < 1e-13:
            completed = step + 1
            break
        previous, vector = vector, target / betas[step]
    tridiagonal = np.diag(alphas[:completed])
    if completed > 1:
        off_diagonal = betas[: completed - 1]
        tridiagonal += np.diag(off_diagonal, 1) + np.diag(off_diagonal, -1)
    eigenvalues = np.linalg.eigvalsh(tridiagonal)
    print("distinct translated core pairs:", len(pairs))
    print("generated translated tangent group order:", len(group))
    print("edge local subgroup orders:", sorted(local_group_orders))
    print("edge tangent-sum dimensions:", sorted(sum_dimensions))
    print("endpoint-choice generated-order distribution:", sorted(choice_orders.items()))
    print("smallest endpoint-choice subgroup order:", smallest_choice[0])
    print("smallest endpoint-choice mask:", smallest_choice[1])
    print(
        "smallest endpoint-choice generators:",
        " ".join(matrix_key(value).hex() for value in smallest_choice[2]),
    )
    print("alternating-projection singular values:")
    print(" ".join(f"{value:.15g}" for value in singular_values[:12]))
    print("constant-orthogonal alternating-projection norm ratios:")
    print(" ".join(f"{sweep}:{ratio:.15g}" for sweep, ratio in decay))
    print("smallest 20 Lanczos Ritz values:")
    print(" ".join(f"{value:.15g}" for value in eigenvalues[:20]))


if __name__ == "__main__":
    main()
