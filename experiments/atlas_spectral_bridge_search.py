"""Test a genuinely coupled bridge between the two exact atlas endpoints.

On the regular representation of H=GL(3,2), the tensor flip is inversion J
and the unique classical boundary alignment is left translation L_k, where k
swaps the first and third coordinates.  Put W=L_k^* J.  Since W^4=1, the
spectral path

    U_t = L_k W^t,  0 <= t <= 1,

is an explicit four-term polynomial in W.  It connects the classical model
U_0=L_k to the tensor flip U_1=J without forming an orthogonal block sum.

This script evaluates the complete distinct endpoint obstruction types that
are supported in H.  The output is a diagnostic for the nonorthogonal route,
not by itself a proof about the full A8 atlas.
"""

import argparse
import json
import sys

import numpy as np

sys.path.insert(0, "experiments")

from atlas_boundary_inner_alignment import aligned_value  # noqa: E402
from atlas_kernel_collision_enumerator import (  # noqa: E402
    enumerate_ball,
    factor_projections,
    lies_in_rank_three_subgroup,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import (  # noqa: E402
    I4,
    gf2_inv,
    gf2_mul,
    matrix_key,
    transvection,
)


def enumerate_h():
    """Enumerate diag(GL(3,2),1) and its exact multiplication indices."""
    generators = [
        transvection(0, 1),
        transvection(1, 0),
        transvection(1, 2),
        transvection(2, 1),
    ]
    elements = [I4.copy()]
    indices = {matrix_key(I4): 0}
    for element in elements:
        for generator in generators:
            target = gf2_mul(element, generator)
            key = matrix_key(target)
            if key not in indices:
                indices[key] = len(elements)
                elements.append(target)
    if len(elements) != 168:
        raise AssertionError("rank-three subgroup enumeration failed")
    return elements, indices, generators


def forward_permutation(elements, indices, left):
    """Return p with L_left delta_j = delta_p[j]."""
    return np.array([
        indices[matrix_key(gf2_mul(left, element))]
        for element in elements
    ], dtype=np.int64)


def inverse_permutation(permutation):
    inverse = np.empty_like(permutation)
    inverse[permutation] = np.arange(len(permutation))
    return inverse


def compose_forward(left, right):
    """Forward permutation for the operator left after right."""
    return left[right]


def spectral_coefficients(t):
    """Coefficients of W^t in the basis 1,W,W^2,W^3.

    We use arguments 0, pi/2, pi, -pi/2 on the fourth roots of unity.
    """
    roots = np.array((1, 1j, -1, -1j), dtype=np.complex128)
    phases = np.exp(1j * t * np.array((0, np.pi / 2, np.pi, -np.pi / 2)))
    return np.array([
        np.sum(phases * roots ** (-power)) / 4
        for power in range(4)
    ])


class SpectralAtlas:
    def __init__(self, elements, indices, generators, t):
        self.elements = elements
        self.indices = indices
        self.dimension = len(elements)
        k = I4.copy()
        k[[0, 2]] = k[[2, 0]]
        self.k = k
        left_k = forward_permutation(elements, indices, k)
        inversion = np.array([
            indices[matrix_key(gf2_inv(element))]
            for element in elements
        ], dtype=np.int64)
        w = compose_forward(left_k, inversion)
        identity = np.arange(self.dimension, dtype=np.int64)
        w_powers = [identity]
        for _ in range(3):
            w_powers.append(compose_forward(w, w_powers[-1]))
        if not np.array_equal(compose_forward(w, w_powers[-1]), identity):
            raise AssertionError("L_k^* J does not have order dividing four")
        self.w_inverse_permutations = [
            inverse_permutation(permutation) for permutation in w_powers
        ]
        self.left_inverse_permutations = {
            matrix_key(element): inverse_permutation(
                forward_permutation(elements, indices, element))
            for element in elements
        }
        self.left_k_inverse = inverse_permutation(left_k)
        self.coefficients = spectral_coefficients(t)
        self.generator_matrices = []
        identity_matrix = np.eye(self.dimension, dtype=np.complex128)
        for factor in (1, 2):
            for generator in generators:
                self.generator_matrices.append(
                    self.apply_letter(factor, generator, identity_matrix))

    def apply_left(self, matrix, vectors):
        key = matrix_key(matrix)
        if key not in self.left_inverse_permutations:
            self.left_inverse_permutations[key] = inverse_permutation(
                forward_permutation(self.elements, self.indices, matrix))
        return vectors[self.left_inverse_permutations[key], :]

    def apply_s(self, vectors, adjoint=False):
        coefficients = (np.conjugate(self.coefficients)
                        if adjoint else self.coefficients)
        # S^* = sum conjugate(c_j) W^{-j}.
        if adjoint:
            powers = [
                self.w_inverse_permutations[(-power) % 4]
                for power in range(4)
            ]
        else:
            powers = self.w_inverse_permutations
        return sum(coefficient * vectors[permutation, :]
                   for coefficient, permutation in zip(coefficients, powers))

    def apply_u(self, vectors):
        return self.apply_s(vectors)[self.left_k_inverse, :]

    def apply_u_adjoint(self, vectors):
        # (L_k S)^* = S^* L_k because k is an involution.
        return self.apply_s(vectors[self.left_k_inverse, :], adjoint=True)

    def apply_letter(self, factor, matrix, vectors):
        if factor == 1:
            return self.apply_left(matrix, vectors)
        vectors = self.apply_u_adjoint(vectors)
        vectors = self.apply_left(matrix, vectors)
        return self.apply_u(vectors)

    def word_matrix(self, word):
        value = np.eye(self.dimension, dtype=np.complex128)
        for factor, matrix in reversed(word):
            value = self.apply_letter(factor, matrix, value)
        return value

    def centrality_defect(self, word):
        value = self.word_matrix(word)
        defects = []
        for generator in self.generator_matrices:
            commutator = value @ generator - generator @ value
            defects.append(np.linalg.norm(commutator, "fro")
                           / np.sqrt(self.dimension))
        return max(defects)


class ImplicitSpectralAtlas(SpectralAtlas):
    """The same path on the 20,160-dimensional regular A8 representation."""

    def __init__(self, elements, indices, generators, t):
        self.elements = elements
        self.indices = indices
        self.dimension = len(elements)
        k = I4.copy()
        k[[0, 2]] = k[[2, 0]]
        self.k = k
        left_k = forward_permutation(elements, indices, k)
        inversion = np.array([
            indices[matrix_key(gf2_inv(element))]
            for element in elements
        ], dtype=np.int64)
        w = compose_forward(left_k, inversion)
        identity = np.arange(self.dimension, dtype=np.int64)
        w_powers = [identity]
        for _ in range(3):
            w_powers.append(compose_forward(w, w_powers[-1]))
        self.w_inverse_permutations = [
            inverse_permutation(permutation) for permutation in w_powers
        ]
        self.left_inverse_permutations = {
            matrix_key(generator): inverse_permutation(
                forward_permutation(elements, indices, generator))
            for generator in generators
        }
        self.left_k_inverse = inverse_permutation(left_k)
        self.coefficients = spectral_coefficients(t)
        self.generators = [(factor, generator)
                           for factor in (1, 2) for generator in generators]

    def apply_word(self, word, vectors):
        value = vectors
        for factor, matrix in reversed(word):
            value = self.apply_letter(factor, matrix, value)
        return value

    def sampled_centrality_defect(self, word, probes):
        generator_probes = [self.apply_letter(factor, generator, probes)
                            for factor, generator in self.generators]
        stacked = np.concatenate([probes] + generator_probes, axis=1)
        word_images = self.apply_word(word, stacked)
        width = probes.shape[1]
        word_probe = word_images[:, :width]
        defects = []
        for index, (factor, generator) in enumerate(self.generators):
            word_generator_probe = word_images[
                :, (index + 1) * width:(index + 2) * width]
            generator_word_probe = self.apply_letter(
                factor, generator, word_probe)
            difference = word_generator_probe - generator_word_probe
            defects.append(float(np.linalg.norm(difference) / np.sqrt(
                self.dimension * width)))
        return max(defects)


def distinct_representatives(words, key_function):
    representatives = {}
    for word in words:
        representatives.setdefault(key_function(word), word)
    return list(representatives.values())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--full-sample", action="store_true")
    parser.add_argument("--full-steps", type=int, default=5)
    args = parser.parse_args()
    elements, indices, generators = enumerate_h()
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    k = I4.copy()
    k[[0, 2]] = k[[2, 0]]
    k_inverse = gf2_inv(k)

    h_supported = [word for word in words if all(
        lies_in_rank_three_subgroup(matrix) for _, matrix in word)]
    boundary = [word for word in h_supported if any(
        matrix_key(projection) != identity_key
        for projection in factor_projections(word))]
    interior_failed = [word for word in h_supported if all(
        matrix_key(projection) == identity_key
        for projection in factor_projections(word)) and aligned_value(
            word, k, k_inverse) != identity_key]

    boundary_representatives = distinct_representatives(
        boundary,
        lambda word: tuple(matrix_key(value)
                           for value in factor_projections(word)),
    )
    interior_representatives = distinct_representatives(
        interior_failed,
        lambda word: aligned_value(word, k, k_inverse),
    )

    rows = []
    for t in np.linspace(0, 1, 9):
        atlas = SpectralAtlas(elements, indices, generators, float(t))
        boundary_defects = [atlas.centrality_defect(word)
                            for word in boundary_representatives]
        interior_defects = [atlas.centrality_defect(word)
                            for word in interior_representatives]
        rows.append({
            "t": float(t),
            "boundary_max": max(boundary_defects, default=0.0),
            "interior_max": max(interior_defects, default=0.0),
            "combined_max": max(boundary_defects + interior_defects,
                                default=0.0),
        })

    result = {
        "subgroup_order": len(elements),
        "h_supported_boundary_words": len(boundary),
        "h_supported_interior_words_failed_by_classical_alignment": (
            len(interior_failed)),
        "distinct_boundary_projection_types": len(boundary_representatives),
        "distinct_classical_interior_images": len(interior_representatives),
        "spectral_path": rows,
    }

    if args.full_sample:
        # Select the shortest endpoint obstructions.  The purpose is to test
        # whether this one-parameter bridge even clears the first necessary
        # full-A8 gate before attempting an expensive complete scan.
        all_elements = [I4.copy()]
        all_indices = {matrix_key(I4): 0}
        all_generators = [
            transvection(row, col)
            for row, col in ((0, 1), (1, 0), (1, 2), (2, 1),
                             (2, 3), (3, 2))
        ]
        for element in all_elements:
            for generator in all_generators:
                target = gf2_mul(element, generator)
                key = matrix_key(target)
                if key not in all_indices:
                    all_indices[key] = len(all_elements)
                    all_elements.append(target)
        if len(all_elements) != 20160:
            raise AssertionError("GL(4,2) enumeration failed")

        all_boundary = [word for word in words if any(
            matrix_key(projection) != identity_key
            for projection in factor_projections(word))]
        all_interior_failed = [word for word in words if all(
            matrix_key(projection) == identity_key
            for projection in factor_projections(word)) and aligned_value(
                word, k, k_inverse) != identity_key]
        boundary_word = min(all_boundary, key=len)
        interior_word = min(all_interior_failed, key=len)
        rng = np.random.default_rng(20260811)
        phases = rng.integers(0, 4, size=(len(all_elements), 2))
        probes = (1j ** phases).astype(np.complex128)
        full_rows = []
        for t in np.linspace(0, 1, args.full_steps):
            atlas = ImplicitSpectralAtlas(
                all_elements, all_indices, all_generators, float(t))
            full_rows.append({
                "t": float(t),
                "shortest_boundary_defect_estimate": (
                    atlas.sampled_centrality_defect(boundary_word, probes)),
                "shortest_interior_defect_estimate": (
                    atlas.sampled_centrality_defect(interior_word, probes)),
            })
        result["full_a8_sample"] = {
            "probe_count": probes.shape[1],
            "boundary_word_length": len(boundary_word),
            "interior_word_length": len(interior_word),
            "rows": full_rows,
        }

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
