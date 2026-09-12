"""Exact characteristic-zero rank-three tangent test in every A8 sector.

The regular-atlas boundary Jacobian is a sum of conjugations by left-regular
``A8`` matrices.  On matrix units ``E_(x,y)``, simultaneous left translation
preserves ``x^-1 y``.  Consequently the full tangent representation is a
multiple of the left regular representation, and it is enough to test each
irreducible representation of ``A8``.

Every irreducible ``A8`` representation occurs in the restriction of an
irreducible ``S8`` representation.  Conjugate partitions give the same
restriction because the sign character is trivial on ``A8``; a
self-conjugate partition contains both split constituents.  Sage's exact
seminormal ``S8`` matrices therefore provide a compact rational certificate.

For every selected partition this script computes

    intersection_w ker(sigma(q_w))

for all 234 signed-prefix derivative elements, and compares it with the
``H=diag(GL(3,2),1)`` fixed space.  Equality in every sector proves the
infinitesimal identity

    ker J_boundary = ker J_H

on the amplified regular representation, with no multiplicity dependence.
"""

import argparse
import json

import numpy as np
from sage.all import (  # pylint: disable=import-error
    Partitions,
    QQ,
    SymmetricGroup,
    SymmetricGroupRepresentation,
    identity_matrix,
    matrix,
    zero_matrix,
)

from atlas_boundary_group_algebra_audit import (
    group_algebra_derivative,
    matrix_from_key,
)
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX, compose
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import (
    I4,
    factor_generators,
    gf2_inv,
    gf2_mul,
    matrix_key,
)


def load_generator_permutations(path):
    with open(path, "r", encoding="utf-8") as stream:
        records = json.load(stream)["matrices"]
    generators = [word[0][1] for _, word in factor_generators()[:6]]
    return [tuple(int(value) - 1 for value in records[
        matrix_key(generator).hex()]) for generator in generators]


def enumerate_isomorphism(generator_permutations):
    """Enumerate GL(4,2) and its compatible natural A8 permutations."""
    generators = [word[0][1] for _, word in factor_generators()[:6]]
    identity_permutation = tuple(range(8))
    matrices = [I4.copy()]
    permutations = [identity_permutation]
    index = {matrix_key(I4): 0}
    for element, element_permutation in zip(matrices, permutations):
        for generator, generator_permutation in zip(
                generators, generator_permutations):
            target = gf2_mul(element, generator)
            target_permutation = compose(
                generator_permutation, element_permutation)
            key = matrix_key(target)
            if key in index:
                if permutations[index[key]] != target_permutation:
                    raise AssertionError("inconsistent exceptional isomorphism")
                continue
            index[key] = len(matrices)
            matrices.append(target)
            permutations.append(target_permutation)
    if len(matrices) != 20160 or len(set(permutations)) != 20160:
        raise AssertionError("GL(4,2) to A8 enumeration failed")
    return {matrix_key(element): permutation
            for element, permutation in zip(matrices, permutations)}


def selected_partitions():
    selected = []
    seen = set()
    for partition in Partitions(8):
        key = tuple(partition)
        conjugate = tuple(partition.conjugate())
        if key in seen:
            continue
        seen.add(key)
        seen.add(conjugate)
        selected.append(key)
    return selected


def common_kernel(matrices, dimension):
    """Return a column basis for the exact common right kernel."""
    basis = identity_matrix(QQ, dimension)
    for operator in matrices:
        if basis.ncols() == 0:
            break
        restricted = operator * basis
        kernel_rows = restricted.right_kernel().basis_matrix()
        basis = basis * kernel_rows.transpose()
    return basis


def sparse_sum(representation_cache, coefficients, dimension):
    result = zero_matrix(QQ, dimension, dimension)
    for key, coefficient in coefficients.items():
        result += coefficient * representation_cache[key]
    return result


def greedy_kernel_certificate(operators, target_dimension):
    """Greedily retain operators until their common kernel has target size."""
    if not operators:
        raise ValueError("operator packet is empty")
    dimension = operators[0].ncols()
    basis = identity_matrix(QQ, dimension)
    selected = []
    remaining = set(range(len(operators)))
    while basis.ncols() > target_dimension:
        best_index = None
        best_basis = None
        for index in sorted(remaining):
            restricted = operators[index] * basis
            kernel_rows = restricted.right_kernel().basis_matrix()
            candidate_basis = basis * kernel_rows.transpose()
            if (best_basis is None
                    or candidate_basis.ncols() < best_basis.ncols()):
                best_index = index
                best_basis = candidate_basis
        if best_basis is None or best_basis.ncols() == basis.ncols():
            raise AssertionError("greedy packet cannot reach target kernel")
        selected.append(best_index)
        remaining.remove(best_index)
        basis = best_basis
    if basis.ncols() != target_dimension:
        raise AssertionError("greedy packet overshot the H-fixed dimension")
    return selected, basis


def h_generators():
    result = []
    for row, column in ((0, 1), (1, 0), (1, 2), (2, 1)):
        element = I4.copy()
        element[row, column] ^= 1
        result.append(element)
    return result


def run(natural_path):
    generator_permutations = load_generator_permutations(natural_path)
    permutation_by_matrix = enumerate_isomorphism(generator_permutations)
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    derivatives = [group_algebra_derivative(
        word, alignment, alignment_inverse) for word in boundary_words()]
    required_keys = {
        key for derivative in derivatives for key in derivative
    }
    required_keys.add(matrix_key(I4))
    for element in h_generators():
        required_keys.add(matrix_key(element))

    symmetric_group = SymmetricGroup(8)
    permutation_elements = {
        key: symmetric_group([
            value + 1 for value in permutation_by_matrix[key]
        ]) for key in required_keys
    }
    records = []
    certificate_indices = set()
    for partition in selected_partitions():
        representation = SymmetricGroupRepresentation(
            list(partition), implementation="seminormal")
        identity = representation(symmetric_group.one())
        dimension = identity.nrows()
        cache = {
            key: representation(permutation_elements[key])
            for key in required_keys
        }
        boundary_operators = [
            sparse_sum(cache, derivative, dimension)
            for derivative in derivatives
        ]
        h_operators = [
            identity - cache[matrix_key(element)]
            for element in h_generators()
        ]
        boundary_kernel = common_kernel(boundary_operators, dimension)
        h_kernel = common_kernel(h_operators, dimension)
        if any(operator * h_kernel != 0 for operator in boundary_operators):
            raise AssertionError("a boundary derivative moves an H-fixed vector")
        greedy_indices, greedy_kernel = greedy_kernel_certificate(
            boundary_operators, h_kernel.ncols())
        certificate_indices.update(greedy_indices)
        if greedy_kernel.ncols() != h_kernel.ncols():
            raise AssertionError("greedy certificate has wrong kernel size")
        if boundary_kernel.ncols():
            h_on_boundary = matrix(QQ, sum(
                [(operator * boundary_kernel).rows()
                 for operator in h_operators], []))
            h_variation_rank = h_on_boundary.rank()
        else:
            h_variation_rank = 0
        records.append({
            "partition": [int(value) for value in partition],
            "dimension": int(dimension),
            "boundary_kernel_dimension": int(boundary_kernel.ncols()),
            "h_fixed_dimension": int(h_kernel.ncols()),
            "h_variation_rank_on_boundary_kernel": int(h_variation_rank),
            "kernels_equal": (
                h_variation_rank == 0
                and boundary_kernel.ncols() == h_kernel.ncols()),
            "greedy_certificate_indices": greedy_indices,
            "greedy_certificate_size": len(greedy_indices),
        })
    return {
        "field": "Q",
        "boundary_relations": len(derivatives),
        "unique_group_elements_in_derivatives": len(required_keys),
        "selected_s8_partitions": len(records),
        "union_greedy_certificate_indices": sorted(certificate_indices),
        "union_greedy_certificate_size": len(certificate_indices),
        "covers_every_a8_irrep": True,
        "records": records,
        "all_boundary_kernels_are_h_fixed": all(
            record["h_variation_rank_on_boundary_kernel"] == 0
            for record in records),
        "all_boundary_kernels_equal_h_fixed_spaces": all(
            record["kernels_equal"] for record in records),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--natural-a8-json", required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.natural_a8_json), indent=2))


if __name__ == "__main__":
    main()
