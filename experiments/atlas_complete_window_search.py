"""Optimize a complete finite-radius Leavitt-atlas centrality window.

The representation sector is the 15-dimensional permutation representation
of each A8 factor, with one relative unitary.  This is a diagnostic sector;
the complete hyperlinearity criterion ultimately uses asymptotically regular
factor characters.  Unlike atlas_two_chart_search.py, however, the relation
window here is exhaustive through a stated word radius.
"""

import argparse
import json

import numpy as np

from atlas_inner_scan import all_gl4
from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import (
    Problem,
    commutator,
    factor_generators,
    matrix_key,
    optimize,
    permutation_rep,
)


class CompleteWindowProblem(Problem):
    def __init__(self, radius, k):
        self.radius = radius
        self.k = k
        self.n = 15 * k
        states, level_sizes = enumerate_ball(radius)
        kernel_words, collision_sizes, _ = spanning_tree_kernel_words(states)
        self.kernel_words = kernel_words
        self.constraint_pairs = []
        self.words = []
        constraint_keys = set()
        for _, generator in factor_generators():
            for kernel_word in kernel_words:
                word = commutator(generator, kernel_word)
                key = tuple((factor, matrix_key(matrix))
                            for factor, matrix in word)
                if word and key not in constraint_keys:
                    constraint_keys.add(key)
                    self.words.append(word)
                    self.constraint_pairs.append((generator, kernel_word))
        if not self.words:
            raise ValueError("the selected radius has no nontrivial constraints")
        self.names = ["complete_r%d_c%d" % (radius, index)
                      for index in range(len(self.words))]
        self.window_summary = {
            "radius": radius,
            "complete_kernel_word_radius": 2 * radius,
            "ball_size": len(states),
            "sphere_sizes": level_sizes,
            "collision_bucket_count": len(collision_sizes),
            "kernel_generators": len(kernel_words),
            "constraints": len(self.words),
        }

        distinct = {}
        for word in self.words:
            for _, matrix in word:
                distinct.setdefault(matrix_key(matrix), matrix)
        eye_k = np.eye(k, dtype=np.complex128)
        self.reps = {
            key: np.kron(permutation_rep(matrix), eye_k)
            for key, matrix in distinct.items()
        }


def matrix_permutation(matrix):
    vectors = ((np.arange(16, dtype=np.uint8)[:, None]
                >> np.arange(3, -1, -1, dtype=np.uint8)) & 1)
    images = (vectors @ matrix.T) & 1
    return (images @ np.array([8, 4, 2, 1], dtype=np.uint8)).astype(np.uint8)


def compose_permutations(left, right):
    if left.ndim == 1:
        return left[right]
    if right.ndim == 1:
        return left[:, right]
    return np.take_along_axis(left, right, axis=1)


def inverse_permutations(permutations):
    return np.argsort(permutations, axis=1).astype(np.uint8)


def exhaustive_inner_scan(problem):
    records = list(all_gl4())
    bits = np.asarray([record[0] for record in records], dtype=np.uint32)
    relatives = np.stack([matrix_permutation(record[1]) for record in records])
    relative_inverses = inverse_permutations(relatives)
    count = len(records)

    fixed_cache = {}
    conjugate_cache = {}

    def aligned(factor, matrix):
        key = matrix_key(matrix)
        fixed = fixed_cache.get(key)
        if fixed is None:
            fixed = matrix_permutation(matrix)
            fixed_cache[key] = fixed
        if factor == 1:
            return np.broadcast_to(fixed, (count, 16))
        conjugate = conjugate_cache.get(key)
        if conjugate is None:
            left = relatives[:, fixed]
            conjugate = compose_permutations(left, relative_inverses)
            conjugate_cache[key] = conjugate
        return conjugate

    def word_values(word):
        value = np.broadcast_to(np.arange(16, dtype=np.uint8), (count, 16))
        for factor, matrix in word:
            value = compose_permutations(value, aligned(factor, matrix))
        return value

    generator_values = {}
    kernel_values = {}
    for generator, kernel_word in problem.constraint_pairs:
        generator_values.setdefault(
            tuple((f, matrix_key(m)) for f, m in generator),
            word_values(generator),
        )
        kernel_values.setdefault(
            tuple((f, matrix_key(m)) for f, m in kernel_word),
            word_values(kernel_word),
        )

    trace_sum = np.zeros(count, dtype=np.float64)
    minimum_trace = np.ones(count, dtype=np.float64)
    exact_count = np.zeros(count, dtype=np.int32)
    identity = np.arange(16, dtype=np.uint8)
    for generator, kernel_word in problem.constraint_pairs:
        generator_key = tuple((f, matrix_key(m)) for f, m in generator)
        kernel_key = tuple((f, matrix_key(m)) for f, m in kernel_word)
        x_value = generator_values[generator_key]
        q_value = kernel_values[kernel_key]
        x_inverse = inverse_permutations(x_value)
        q_inverse = inverse_permutations(q_value)
        value = compose_permutations(x_value, q_value)
        value = compose_permutations(value, x_inverse)
        value = compose_permutations(value, q_inverse)
        fixed_nonzero = np.count_nonzero(value[:, 1:] == identity[1:], axis=1)
        traces = fixed_nonzero / 15.0
        trace_sum += traces
        minimum_trace = np.minimum(minimum_trace, traces)
        exact_count += fixed_nonzero == 15

    mean_trace = trace_sum / len(problem.constraint_pairs)
    max_defect = np.sqrt(2.0 - 2.0 * minimum_trace)
    rms_defect = np.sqrt(2.0 - 2.0 * mean_trace)
    order = np.lexsort((-mean_trace, max_defect))
    best_index = int(order[0])
    best_mask = ((max_defect == max_defect[best_index])
                 & (rms_defect == rms_defect[best_index]))
    unique_counts, multiplicities = np.unique(exact_count, return_counts=True)
    return {
        "alignments": count,
        "best_count": int(np.count_nonzero(best_mask)),
        "best": {
            "bits": int(bits[best_index]),
            "exact_constraints": int(exact_count[best_index]),
            "mean_trace": float(mean_trace[best_index]),
            "rms_defect": float(rms_defect[best_index]),
            "max_defect": float(max_defect[best_index]),
        },
        "exact_satisfaction_histogram": [
            [int(value), int(multiplicity)]
            for value, multiplicity in zip(unique_counts, multiplicities)
        ],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=2)
    parser.add_argument("--k", type=int, default=1)
    parser.add_argument("--iters", type=int, default=500)
    parser.add_argument("--seeds", type=int, default=4)
    parser.add_argument("--batch", type=int, default=32)
    parser.add_argument("--report-every", type=int, default=100)
    parser.add_argument("--focus-every", type=int, default=10)
    parser.add_argument("--identity-start", action="store_true")
    parser.add_argument("--inner-bits", type=int)
    parser.add_argument("--inner-scan", action="store_true")
    parser.add_argument("--save", type=str)
    args = parser.parse_args()

    problem = CompleteWindowProblem(args.radius, args.k)
    print(json.dumps({"event": "window", **problem.window_summary}), flush=True)
    if args.inner_scan:
        if args.k != 1:
            raise ValueError("the exact inner scan is independent of amplification; use k=1")
        print(json.dumps({"event": "inner_scan", **problem.window_summary,
                          **exhaustive_inner_scan(problem)}), flush=True)
        return
    if args.identity_start and args.inner_bits is not None:
        raise ValueError("choose at most one explicit starting alignment")
    if args.inner_bits is not None:
        flat = np.array([(args.inner_bits >> index) & 1 for index in range(16)],
                        dtype=np.uint8)
        initial = np.kron(permutation_rep(flat.reshape(4, 4)),
                          np.eye(args.k, dtype=np.complex128))
    elif args.identity_start:
        initial = np.eye(problem.n, dtype=np.complex128)
    else:
        initial = None
    results = []
    for seed in range(args.seeds):
        unitary, diagnostics = optimize(
            problem,
            1729 + seed,
            args.iters,
            args.batch,
            args.report_every,
            initial,
            args.focus_every,
        )
        results.append((unitary, diagnostics))

    best_unitary, best = min(
        results, key=lambda item: (item[1]["max_defect"], item[1]["rms_defect"])
    )
    if args.save:
        np.save(args.save, best_unitary)
    print(json.dumps({"event": "final", **problem.window_summary,
                      "best": best}), flush=True)


if __name__ == "__main__":
    main()
