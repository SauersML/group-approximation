"""Probe the finite-order geodesic between two exact atlas endpoints.

On the regular A8 representation, J is inversion (the tensor flip) and L_k
is the unique inner alignment that kills the complete radius-five boundary.
For D=J L_k one has D^4=1.  Every square-root branch F^2=D is therefore an
exact degree-three polynomial in D, and U=J F is a structured midpoint
between the two endpoints.

This script uses implicit permutations and Hutchinson trace probes; it never
forms a 20160-square matrix.  It is a discovery calculation, not an exact
certificate.  Any promising branch should be re-evaluated in the rational
cyclotomic group algebra.
"""

import argparse
import cmath
import json
import time

import numpy as np

from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


def compose(left, right):
    """Targets of the operator product P_left P_right."""
    return left[right]


def apply_permutation(state, targets):
    answer = np.empty_like(state)
    answer[targets] = state
    return answer


def polynomial_coefficients(values):
    """Coefficients c_r with f(D)=sum_r c_r D^r for D^4=1."""
    roots = [cmath.exp(2j * cmath.pi * index / 4) for index in range(4)]
    return np.array([
        sum(values[index] * roots[index] ** (-power)
            for index in range(4)) / 4
        for power in range(4)
    ], dtype=np.complex128)


def square_root_branches():
    roots = [cmath.exp(1j * cmath.pi * index / 4) for index in range(4)]
    branches = []
    # A simultaneous sign change is a scalar and disappears under conjugacy.
    for bits in range(8):
        values = [roots[0]]
        values.extend(
            roots[index] * (-1 if bits & (1 << (index - 1)) else 1)
            for index in range(1, 4)
        )
        branches.append(("root_%03d" % bits,
                         polynomial_coefficients(values)))
    return branches


class RegularPathModel:
    def __init__(self, elements, alignment):
        self.elements = elements
        self.indices = {matrix_key(element): index
                        for index, element in enumerate(elements)}
        self.left_cache = {}
        inversion = np.array([
            self.indices[matrix_key(gf2_inv(element))]
            for element in elements
        ], dtype=np.int64)
        left_alignment = self.left(alignment)
        self.j = inversion
        self.d = compose(inversion, left_alignment)
        identity = np.arange(len(elements), dtype=np.int64)
        powers = [identity]
        for _ in range(3):
            powers.append(compose(self.d, powers[-1]))
        if not np.array_equal(compose(self.d, powers[-1]), identity):
            raise AssertionError("J L_k does not have order dividing four")
        self.d_powers = powers

    def left(self, matrix):
        key = matrix_key(matrix)
        if key not in self.left_cache:
            self.left_cache[key] = np.array([
                self.indices[matrix_key(gf2_mul(matrix, element))]
                for element in self.elements
            ], dtype=np.int64)
        return self.left_cache[key]

    def apply_polynomial(self, state, coefficients, adjoint=False):
        answer = np.zeros_like(state)
        for power, coefficient in enumerate(coefficients):
            if adjoint:
                coefficient = np.conjugate(coefficient)
                permutation = self.d_powers[(-power) % 4]
            else:
                permutation = self.d_powers[power]
            answer += coefficient * apply_permutation(state, permutation)
        return answer

    def apply_u(self, state, coefficients):
        return apply_permutation(
            self.apply_polynomial(state, coefficients), self.j)

    def apply_u_adjoint(self, state, coefficients):
        return self.apply_polynomial(
            apply_permutation(state, self.j), coefficients, adjoint=True)

    def apply_word(self, word, state, coefficients):
        answer = state
        for factor, matrix in reversed(word):
            if factor == 1:
                answer = apply_permutation(answer, self.left(matrix))
            else:
                answer = self.apply_u_adjoint(answer, coefficients)
                answer = apply_permutation(answer, self.left(matrix))
                answer = self.apply_u(answer, coefficients)
        return answer


def evenly_spaced(values, count):
    if count >= len(values):
        return list(values)
    indices = np.linspace(0, len(values) - 1, count, dtype=int)
    return [values[index] for index in indices]


def aligned_value(word, alignment, inverse_alignment):
    value = I4.copy()
    for factor, matrix in word:
        if factor == 2:
            matrix = gf2_mul(
                gf2_mul(alignment, matrix), inverse_alignment)
        value = gf2_mul(value, matrix)
    return value


def run(args):
    started = time.time()
    states, sphere_sizes = enumerate_ball(args.radius)
    words, _, _ = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    boundary = []
    tensor_controls = []
    for word in words:
        projections = factor_projections(word)
        (boundary if any(matrix_key(value) != identity_key
                         for value in projections) else tensor_controls).append(word)

    elements = enumerate_gl4()
    alignment = np.array([
        [0, 0, 1, 0],
        [0, 1, 0, 0],
        [1, 0, 0, 0],
        [0, 0, 0, 1],
    ], dtype=np.uint8)
    inverse_alignment = gf2_inv(alignment)
    wall_failures = [
        word for word in tensor_controls
        if matrix_key(aligned_value(word, alignment, inverse_alignment))
        != identity_key
    ]
    shared_controls = [
        word for word in tensor_controls
        if matrix_key(aligned_value(word, alignment, inverse_alignment))
        == identity_key
    ]
    if len(wall_failures) != 6394:
        raise AssertionError("wall-alignment failure set changed")
    model = RegularPathModel(elements, alignment)
    selected_boundary = evenly_spaced(boundary, args.boundary_samples)
    selected_wall_failures = evenly_spaced(
        wall_failures, args.wall_failure_samples)
    selected_shared = evenly_spaced(shared_controls, args.shared_samples)
    selected = [("boundary", word) for word in selected_boundary]
    selected.extend(("wall_failure", word) for word in selected_wall_failures)
    selected.extend(("shared", word) for word in selected_shared)

    rng = np.random.default_rng(args.seed)
    probes = rng.choice((-1.0, 1.0),
                        size=(len(elements), args.probes)).astype(np.complex128)
    probe_norm = float(probes.size)

    branches = [
        ("tensor_flip", np.array((1, 0, 0, 0), dtype=np.complex128)),
        ("wall_alignment", np.array((0, 1, 0, 0), dtype=np.complex128)),
    ]
    branches.extend(square_root_branches())
    results = []
    for label, coefficients in branches:
        traces = []
        kinds = []
        for kind, word in selected:
            image = model.apply_word(word, probes, coefficients)
            trace = np.vdot(probes, image) / probe_norm
            traces.append(trace)
            kinds.append(kind)
        projective_losses = np.array([
            max(0.0, 1.0 - min(1.0, abs(trace) ** 2)) for trace in traces
        ])
        boundary_losses = projective_losses[
            np.array([kind == "boundary" for kind in kinds])]
        wall_losses = projective_losses[
            np.array([kind == "wall_failure" for kind in kinds])]
        shared_losses = projective_losses[
            np.array([kind == "shared" for kind in kinds])]
        results.append({
            "label": label,
            "coefficients": [[float(value.real), float(value.imag)]
                             for value in coefficients],
            "mean_projective_loss": float(projective_losses.mean()),
            "max_projective_loss": float(projective_losses.max()),
            "boundary_mean_loss": float(boundary_losses.mean()),
            "boundary_max_loss": float(boundary_losses.max()),
            "wall_failure_mean_loss": float(wall_losses.mean()),
            "wall_failure_max_loss": float(wall_losses.max()),
            "shared_mean_loss": float(shared_losses.mean()),
            "shared_max_loss": float(shared_losses.max()),
            "minimum_trace_modulus": float(min(abs(value) for value in traces)),
        })
    results.sort(key=lambda item: (
        item["max_projective_loss"], item["mean_projective_loss"]))
    return {
        "radius": args.radius,
        "sphere_sizes": sphere_sizes,
        "kernel_words": len(words),
        "boundary_words": len(boundary),
        "tensor_control_words": len(tensor_controls),
        "wall_failure_words": len(wall_failures),
        "shared_control_words": len(shared_controls),
        "sampled_boundary_words": len(selected_boundary),
        "sampled_wall_failure_words": len(selected_wall_failures),
        "sampled_shared_control_words": len(selected_shared),
        "probes": args.probes,
        "seed": args.seed,
        "relative_endpoint_order": 4,
        "results": results,
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=5)
    parser.add_argument("--boundary-samples", type=int, default=8)
    parser.add_argument("--wall-failure-samples", type=int, default=8)
    parser.add_argument("--shared-samples", type=int, default=4)
    parser.add_argument("--probes", type=int, default=1)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--output")
    args = parser.parse_args()
    result = run(args)
    encoded = json.dumps(result, indent=2)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as stream:
            stream.write(encoded + "\n")
    print(encoded)


if __name__ == "__main__":
    main()
