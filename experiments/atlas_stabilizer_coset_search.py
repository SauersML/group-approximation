"""Implicit regular-atlas search in an index-15 stabilizer ansatz.

For a point or hyperplane stabilizer M<GL(4,F2), identify

    l2(GL(4,F2)) = l2(M) tensor C^15

using left cosets.  The relative unitary U=(I_M tensor V)J has exact regular
factor restrictions and only V in O(15) is optimized.  Full 20160-square
matrices are never formed: group elements act by permutations and V acts in
1344 identical small blocks.

The objective is a stochastic trace estimate on sampled complete radius-five
centrality constraints.  It is a discovery search, not a certificate.
"""

import argparse
import json
import random
import time

import numpy as np
import torch

from atlas_kernel_collision_enumerator import factor_projections
from atlas_two_chart_search import (
    I4,
    commutator,
    factor_generators,
    gf2_inv,
    gf2_mul,
    matrix_key,
)


def enumerate_group():
    generators = [word[0][1] for _name, word in factor_generators()[:6]]
    elements = [I4.copy()]
    indices = {matrix_key(I4): 0}
    cursor = 0
    while cursor < len(elements):
        value = elements[cursor]
        cursor += 1
        for generator in generators:
            target = gf2_mul(value, generator)
            key = matrix_key(target)
            if key not in indices:
                indices[key] = len(elements)
                elements.append(target)
    if len(elements) != 20160:
        raise AssertionError("selected generators did not enumerate A8")
    return elements, indices


def fixed_vector(bits):
    return np.array([(bits >> index) & 1 for index in range(4)],
                    dtype=np.uint8)


def in_stabilizer(matrix, kind, vector):
    image = ((matrix @ vector) & 1 if kind == "point"
             else (vector @ matrix) & 1)
    return np.array_equal(image, vector)


def coset_coordinates(elements, indices, kind, vector):
    subgroup = [value for value in elements
                if in_stabilizer(value, kind, vector)]
    if len(subgroup) != 1344:
        raise AssertionError("stabilizer does not have order 1344")
    coordinates = {}
    representatives = []
    for candidate in elements:
        candidate_key = matrix_key(candidate)
        if candidate_key in coordinates:
            continue
        coset = len(representatives)
        representatives.append(candidate)
        for internal, subgroup_element in enumerate(subgroup):
            value = gf2_mul(subgroup_element, candidate)
            key = matrix_key(value)
            if key in coordinates:
                raise AssertionError("left cosets overlap")
            coordinates[key] = (internal, coset)
    if len(representatives) != 15 or len(coordinates) != len(elements):
        raise AssertionError("bad stabilizer coset decomposition")
    ordered = [None] * len(elements)
    for key, group_index in indices.items():
        internal, coset = coordinates[key]
        ordered[internal * 15 + coset] = elements[group_index]
    if any(value is None for value in ordered):
        raise AssertionError("incomplete tensor coordinate order")
    ordered_index = {matrix_key(value): index
                     for index, value in enumerate(ordered)}
    return ordered, ordered_index


def decode_word(encoded):
    return [
        (item["factor"], np.frombuffer(
            bytes.fromhex(item["matrix_f2_hex"]), dtype=np.uint8
        ).reshape(4, 4).copy())
        for item in encoded
    ]


def matrix_commutator(left, right):
    return gf2_mul(
        gf2_mul(gf2_mul(left, right), gf2_inv(left)), gf2_inv(right))


def exposing_generator(projections, generators):
    identity_key = matrix_key(I4)
    for generator in generators:
        factor, matrix = generator[0]
        projection = projections[factor - 1]
        if (matrix_key(projection) != identity_key
                and matrix_key(matrix_commutator(
                    matrix, projection)) != identity_key):
            return generator
    raise AssertionError("nontrivial projection pair has no exposing generator")


class ImplicitModel:
    def __init__(self, ordered, ordered_index, device):
        self.ordered = ordered
        self.ordered_index = ordered_index
        self.device = device
        self.left = {}
        self.right = {}

    def permutation(self, matrix, side):
        cache = self.left if side == "left" else self.right
        key = matrix_key(matrix)
        if key not in cache:
            inverse = gf2_inv(matrix)
            targets = [
                gf2_mul(matrix, value) if side == "left"
                else gf2_mul(value, inverse)
                for value in self.ordered
            ]
            cache[key] = torch.tensor(
                [self.ordered_index[matrix_key(value)] for value in targets],
                dtype=torch.long, device=self.device)
        return cache[key]

    @staticmethod
    def apply_permutation(state, permutation):
        return torch.zeros_like(state).index_copy(0, permutation, state)

    @staticmethod
    def apply_small_unitary(state, unitary):
        shaped = state.reshape(1344, 15, -1)
        return torch.einsum("cd,hdb->hcb", unitary, shaped).reshape_as(state)

    def apply_word(self, word, state, unitary):
        value = state
        for factor, matrix in reversed(word):
            if factor == 1:
                value = self.apply_permutation(
                    value, self.permutation(matrix, "left"))
            else:
                value = self.apply_small_unitary(value, unitary.T)
                value = self.apply_permutation(
                    value, self.permutation(matrix, "right"))
                value = self.apply_small_unitary(value, unitary)
        return value


def run(args):
    torch.set_num_threads(args.threads)
    torch.manual_seed(args.seed)
    random.seed(args.seed)
    started = time.time()
    with open(args.artifact, "r", encoding="utf-8") as stream:
        artifact = json.load(stream)
    words = [decode_word(encoded)
             for encoded in artifact["kernel_generators"]]
    identity_key = matrix_key(I4)
    failing = []
    satisfied = []
    for word in words:
        projections = factor_projections(word)
        if any(matrix_key(value) != identity_key for value in projections):
            failing.append((word, projections))
        else:
            satisfied.append(word)
    if len(failing) != 234:
        raise AssertionError("artifact does not have the radius-five boundary")

    elements, indices = enumerate_group()
    ordered, ordered_index = coset_coordinates(
        elements, indices, args.kind, fixed_vector(args.vector_bits))
    model = ImplicitModel(ordered, ordered_index, torch.device("cpu"))
    generators = [word for _name, word in factor_generators()]

    parameter = torch.randn(15, 15, dtype=torch.float64) * args.initial_scale
    parameter.requires_grad_()
    optimizer = torch.optim.Adam([parameter], lr=args.learning_rate)
    probe = torch.randint(0, 2, (20160, args.probes), dtype=torch.float64)
    probe = 2.0 * probe - 1.0
    probe_norm = float(probe.numel())
    constraints = []
    for _ in range(args.batch_size // 2):
        failing_word, projections = random.choice(failing)
        constraints.append(commutator(
            exposing_generator(projections, generators), failing_word))
        constraints.append(commutator(
            random.choice(generators), random.choice(satisfied)))
    history = []
    best = float("inf")
    for iteration in range(args.iterations + 1):
        optimizer.zero_grad()
        skew = parameter - parameter.T
        unitary = torch.matrix_exp(skew)
        losses = []
        for constraint in constraints:
            image = model.apply_word(constraint, probe, unitary)
            trace = torch.sum(probe * image) / probe_norm
            losses.append(2.0 - 2.0 * trace)
        loss = torch.stack(losses).mean()
        value = float(loss.detach())
        best = min(best, value)
        if iteration % args.report_every == 0 or iteration == args.iterations:
            history.append({
                "iteration": iteration,
                "sampled_defect_squared": value,
                "best_sampled_defect_squared": best,
                "orthogonality_error": float(torch.linalg.norm(
                    unitary.T @ unitary - torch.eye(15))),
            })
        if iteration != args.iterations:
            loss.backward()
            optimizer.step()
    return {
        "kind": args.kind,
        "fixed_vector_bits": args.vector_bits,
        "regular_dimension": 20160,
        "stabilizer_order": 1344,
        "coset_dimension": 15,
        "failing_kernel_words": len(failing),
        "control_kernel_words": len(satisfied),
        "iterations": args.iterations,
        "batch_size": args.batch_size,
        "probes": args.probes,
        "seed": args.seed,
        "history": history,
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", required=True)
    parser.add_argument("--kind", choices=("point", "hyperplane"),
                        default="point")
    parser.add_argument("--vector-bits", type=int, default=3)
    parser.add_argument("--iterations", type=int, default=10)
    parser.add_argument("--batch-size", type=int, default=4)
    parser.add_argument("--probes", type=int, default=1)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--initial-scale", type=float, default=0.02)
    parser.add_argument("--learning-rate", type=float, default=0.01)
    parser.add_argument("--report-every", type=int, default=1)
    parser.add_argument("--threads", type=int, default=4)
    args = parser.parse_args()
    if args.batch_size < 2 or args.batch_size % 2:
        parser.error("--batch-size must be a positive even integer")
    print(json.dumps(run(args)))


if __name__ == "__main__":
    main()
