"""Instantiate and score the exact 64-dimensional Clifford atlas block.

Run with SageMath.  GAP supplies GL(4,2) ~= A8, and Sage's orthogonal Young
representation of shape (5,2,1) supplies the 64-dimensional irrep.  The
script constructs the Pauli intertwiner from FALSE_LOCAL_CLIFFORD_ATLAS.md,
verifies q=-i and the three commutators=-1, then scores either the 234-word
tensor-flip boundary or the complete collision-tree artifact.
"""

import argparse
import json
import math
import time

import numpy as np
from sage.all import GF, SymmetricGroup, libgap, matrix
from sage.combinat.symmetric_group_representations import (
    SymmetricGroupRepresentation,
)

from atlas_kernel_collision_enumerator import factor_projections
from atlas_two_chart_search import (
    I4,
    factor_generators,
    gf2_inv,
    gf2_mul,
    matrix_key,
)


class CliffordBlock:
    def __init__(self, seed):
        group = libgap.GL(4, 2)
        alternating = libgap.AlternatingGroup(8)
        self.isomorphism = libgap.IsomorphismGroups(group, alternating)
        self.symmetric = SymmetricGroup(8)
        young = SymmetricGroupRepresentation(
            [5, 2, 1], implementation="orthogonal")
        self.simple = [
            np.array(
                young.representation_matrix_for_simple_transposition(
                    index).numerical_approx(digits=16),
                dtype=np.complex128,
            )
            for index in range(1, 8)
        ]
        self.cache = {}
        self.relative = self._construct_relative(seed)

    def representation(self, value):
        key = matrix_key(value)
        if key not in self.cache:
            gap_matrix = libgap(matrix(GF(2), value.tolist()))
            permutation = self.symmetric(
                libgap.Image(self.isomorphism, gap_matrix).sage())
            result = np.eye(64, dtype=np.complex128)
            for index in permutation.reduced_word():
                result = result @ self.simple[index - 1]
            self.cache[key] = result
        return self.cache[key]

    @staticmethod
    def local_matrices():
        identity = np.eye(4, dtype=np.uint8)
        first = identity.copy()
        first[:2, :2] = np.array(((0, 1), (1, 0)), dtype=np.uint8)
        second = identity.copy()
        second[:2, :2] = np.array(((1, 0), (1, 1)), dtype=np.uint8)
        lamp = identity.copy()
        lamp[:2, :2] = np.array(((1, 1), (0, 1)), dtype=np.uint8)
        return first, second, lamp

    @staticmethod
    def evaluate_letters(word, first, second):
        result = np.eye(64, dtype=np.complex128)
        for letter in word:
            result = result @ (first if letter == "s" else second)
        return result

    def _construct_relative(self, seed):
        first, second, lamp = self.local_matrices()
        rho_first = self.representation(first)
        rho_second = self.representation(second)
        rho_lamp = self.representation(lamp)

        pauli_x = np.array(((0, 1), (1, 0)), dtype=np.complex128)
        pauli_y = np.array(((0, -1j), (1j, 0)), dtype=np.complex128)
        pauli_z = np.diag((1, -1)).astype(np.complex128)
        sigma_first = (pauli_x + pauli_y) / math.sqrt(2.0)
        sigma_second = -(pauli_x + pauli_z) / math.sqrt(2.0)
        alpha_first = np.eye(32, dtype=np.complex128)
        alpha_second = np.eye(32, dtype=np.complex128)
        for copy in range(10):
            block = slice(12 + 2 * copy, 14 + 2 * copy)
            alpha_first[block, block] = sigma_first
            alpha_second[block, block] = sigma_second
        target_first = np.kron(sigma_first, alpha_first)
        target_second = np.kron(sigma_second, alpha_second)

        subgroup_words = ("", "s", "t", "st", "ts", "sts")
        pairs = [
            (
                self.evaluate_letters(word, rho_first, rho_second),
                self.evaluate_letters(word, target_first, target_second),
            )
            for word in subgroup_words
        ]
        random = np.random.default_rng(seed)
        seed_matrix = (
            random.normal(size=(64, 64))
            + 1j * random.normal(size=(64, 64))
        )
        averaged = sum(
            target @ seed_matrix @ source.conj().T
            for source, target in pairs
        )
        left, _singular, right = np.linalg.svd(averaged)
        intertwiner = left @ right
        desired_lamp = (
            intertwiner.conj().T
            @ np.kron(pauli_x, np.eye(32))
            @ intertwiner
        )
        source_values, source_vectors = np.linalg.eigh(rho_lamp)
        target_values, target_vectors = np.linalg.eigh(desired_lamp)
        return (
            target_vectors[:, np.argsort(target_values)]
            @ source_vectors[:, np.argsort(source_values)].conj().T
        )

    def first_chart(self, value):
        return self.representation(value)

    def second_chart(self, value):
        representation = self.representation(value)
        return self.relative @ representation @ self.relative.conj().T

    def word_value(self, word):
        result = np.eye(64, dtype=np.complex128)
        for factor, value in word:
            result = result @ (
                self.first_chart(value) if factor == 1
                else self.second_chart(value)
            )
        return result

    def local_diagnostics(self):
        first, second, lamp = self.local_matrices()
        first_value = self.first_chart(first)
        second_value = self.first_chart(second)
        lamp_value = self.second_chart(lamp)
        conjugates = (
            lamp_value,
            first_value @ lamp_value @ first_value.conj().T,
            (first_value @ second_value) @ lamp_value
            @ (first_value @ second_value).conj().T,
        )
        q_value = conjugates[1] @ conjugates[2] @ conjugates[0]
        commutator_errors = []
        for left, right in (
            (conjugates[0], conjugates[1]),
            (conjugates[0], conjugates[2]),
            (conjugates[1], conjugates[2]),
        ):
            commutator = (
                left @ right @ left.conj().T @ right.conj().T)
            commutator_errors.append(float(np.linalg.norm(
                commutator + np.eye(64))))
        return {
            "q_plus_i_frobenius": float(np.linalg.norm(
                q_value + 1j * np.eye(64))),
            "commutator_plus_identity_frobenius": commutator_errors,
            "relative_unitarity_error": float(np.linalg.norm(
                self.relative.conj().T @ self.relative - np.eye(64))),
        }


def decode_word(encoded):
    return [
        (item["factor"], np.frombuffer(
            bytes.fromhex(item["matrix_f2_hex"]), dtype=np.uint8
        ).reshape(4, 4).copy())
        for item in encoded
    ]


def run(args):
    started = time.time()
    block = CliffordBlock(args.seed)
    with open(args.artifact, "r", encoding="utf-8") as stream:
        artifact = json.load(stream)
    words = [decode_word(encoded)
             for encoded in artifact["kernel_generators"]]
    identity_key = matrix_key(I4)
    records = []
    for word in words:
        projections = factor_projections(word)
        label = ",".join(matrix_key(value).hex() for value in projections)
        records.append((word, projections, label))
    if args.scope == "boundary":
        records = [
            record for record in records
            if any(matrix_key(value) != identity_key
                   for value in record[1])
        ]
    generators = [word[0] for _name, word in factor_generators()]
    generator_values = [
        block.first_chart(value) if factor == 1
        else block.second_chart(value)
        for factor, value in generators
    ]
    defect_sum = 0.0
    defect_max = 0.0
    central_words = 0
    worst = []
    pair_stats = {}
    for index, (word, _projections, label) in enumerate(records):
        value = block.word_value(word)
        word_max = 0.0
        for generator in generator_values:
            commutator = (
                generator @ value @ generator.conj().T @ value.conj().T)
            defect_squared = float(
                np.linalg.norm(commutator - np.eye(64)) ** 2 / 64.0)
            defect_sum += defect_squared
            defect_max = max(defect_max, defect_squared)
            word_max = max(word_max, defect_squared)
        if word_max < args.tolerance:
            central_words += 1
        stats = pair_stats.setdefault(label, {
            "words": 0,
            "central_words": 0,
            "maximum_defect_squared": 0.0,
        })
        stats["words"] += 1
        stats["central_words"] += int(word_max < args.tolerance)
        stats["maximum_defect_squared"] = max(
            stats["maximum_defect_squared"], word_max)
        worst.append((word_max, index))
    worst.sort(reverse=True)
    return {
        "scope": args.scope,
        "kernel_words_scored": len(records),
        "centrality_constraints_scored": 12 * len(records),
        "central_kernel_words": central_words,
        "mean_defect_squared": defect_sum / (12 * len(records)),
        "rms_defect": math.sqrt(defect_sum / (12 * len(records))),
        "maximum_defect_squared": defect_max,
        "maximum_defect": math.sqrt(defect_max),
        "worst_word_indices": [
            {"index": index, "maximum_defect_squared": value}
            for value, index in worst[:10]
        ],
        "projection_pair_statistics": pair_stats,
        "local_clifford": block.local_diagnostics(),
        "representation_cache_size": len(block.cache),
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", required=True)
    parser.add_argument("--scope", choices=("boundary", "all"),
                        default="boundary")
    parser.add_argument("--seed", type=int, default=4)
    parser.add_argument("--tolerance", type=float, default=1e-20)
    args = parser.parse_args()
    print(json.dumps(run(args)))


if __name__ == "__main__":
    main()
