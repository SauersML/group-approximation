"""Refine the 64D Clifford block while preserving its Pauli lamp exactly.

Run with SageMath.  All relative unitaries U C with C commuting with the
second-chart involution have the same Pauli image of that involution, hence
retain q=-i and the local Clifford commutators.  This script projects trace
gradients to that U(32) x U(32) tangent space and optimizes the 25 boundary
words in the uniquely repaired projection-pair class.
"""

import argparse
import json
import time

import numpy as np

from atlas_clifford_block import CliffordBlock, decode_word
from atlas_kernel_collision_enumerator import factor_projections
from atlas_two_chart_search import (
    I4,
    commutator,
    factor_generators,
    matrix_key,
)


def cayley_left(unitary, direction, step):
    identity = np.eye(unitary.shape[0], dtype=np.complex128)
    half = 0.5 * step * direction
    return np.linalg.solve(identity - half, (identity + half) @ unitary)


def factors(block, word, relative):
    adjoint = relative.conj().T
    return [
        block.representation(value) if factor == 1
        else relative @ block.representation(value) @ adjoint
        for factor, value in word
    ]


def trace_and_gradient(block, word, relative, need_gradient):
    word_factors = factors(block, word, relative)
    length = len(word_factors)
    prefix = [np.eye(64, dtype=np.complex128)]
    for value in word_factors:
        prefix.append(prefix[-1] @ value)
    trace = float(np.trace(prefix[-1]).real / 64.0)
    if not need_gradient:
        return trace, None
    suffix = [None] * (length + 1)
    suffix[length] = np.eye(64, dtype=np.complex128)
    for position in range(length - 1, -1, -1):
        suffix[position] = word_factors[position] @ suffix[position + 1]
    gradient = np.zeros((64, 64), dtype=np.complex128)
    for position, (factor, _value) in enumerate(word):
        if factor == 2:
            chart_value = word_factors[position]
            rest = suffix[position + 1] @ prefix[position]
            gradient += chart_value @ rest - rest @ chart_value
    return trace, gradient / 64.0


def traces(block, constraints, relative):
    return np.array([
        trace_and_gradient(block, word, relative, False)[0]
        for word in constraints
    ])


def diagnostics(block, constraints, relative):
    values = traces(block, constraints, relative)
    defects = np.sqrt(np.maximum(0.0, 2.0 - 2.0 * values))
    return {
        "mean_trace": float(values.mean()),
        "rms_defect": float(np.sqrt(np.mean(defects ** 2))),
        "maximum_defect": float(defects.max()),
        "constraints_below_1e-8": int(np.sum(defects < 1e-8)),
    }


def score(block, constraints, relative, indices, need_gradient):
    total = 0.0
    gradient = np.zeros((64, 64), dtype=np.complex128)
    for index in indices:
        value, derivative = trace_and_gradient(
            block, constraints[index], relative, need_gradient)
        total += value
        if need_gradient:
            gradient += derivative
    count = len(indices)
    return total / count, gradient / count


def run(args):
    started = time.time()
    block = CliffordBlock(args.seed)
    with open(args.artifact, "r", encoding="utf-8") as stream:
        artifact = json.load(stream)
    boundary = []
    identity_key = matrix_key(I4)
    for encoded in artifact["kernel_generators"]:
        word = decode_word(encoded)
        projections = factor_projections(word)
        if all(matrix_key(value) == identity_key for value in projections):
            continue
        label = ",".join(matrix_key(value).hex() for value in projections)
        boundary.append((word, label))

    generators = [word for _name, word in factor_generators()]
    group_counts = {}
    for word, label in boundary:
        value = block.word_value(word)
        maximum = 0.0
        for generator in generators:
            generator_value = block.word_value(generator)
            commutator_value = (
                generator_value @ value @ generator_value.conj().T
                @ value.conj().T)
            maximum = max(maximum, float(np.linalg.norm(
                commutator_value - np.eye(64)) ** 2 / 64.0))
        stats = group_counts.setdefault(label, [0, 0])
        stats[0] += 1
        stats[1] += int(maximum < 1e-20)
    target_label = max(group_counts, key=lambda label: group_counts[label][1])
    target_words = [word for word, label in boundary if label == target_label]
    constraints = [commutator(generator, word)
                   for word in target_words for generator in generators]

    _first, _second, lamp = block.local_matrices()
    lamp_image = block.second_chart(lamp)
    plus = 0.5 * (np.eye(64) + lamp_image)
    minus = 0.5 * (np.eye(64) - lamp_image)
    relative = block.relative.copy()
    history = [{"iteration": 0, **diagnostics(block, constraints, relative)}]
    for iteration in range(1, args.iterations + 1):
        values = traces(block, constraints, relative)
        active = np.argsort(values)[:min(args.batch_size, len(values))]
        old, gradient = score(
            block, constraints, relative, active, True)
        skew = 0.5 * (gradient - gradient.conj().T)
        direction = -(plus @ skew @ plus + minus @ skew @ minus)
        accepted = False
        for step in (3.0, 1.0, 0.3, 0.1, 0.03, 0.01):
            candidate = cayley_left(relative, direction, step)
            new, _gradient = score(
                block, constraints, candidate, active, False)
            if new > old + 1e-12:
                relative = candidate
                accepted = True
                break
        if iteration % args.report_every == 0 or iteration == args.iterations:
            history.append({
                "iteration": iteration,
                "accepted": accepted,
                **diagnostics(block, constraints, relative),
                "lamp_preservation_error": float(np.linalg.norm(
                    relative @ block.representation(lamp)
                    @ relative.conj().T - lamp_image)),
            })
    block.relative = relative
    return {
        "target_projection_pair": target_label,
        "target_words": len(target_words),
        "constraints": len(constraints),
        "initially_central_target_words": group_counts[target_label][1],
        "iterations": args.iterations,
        "history": history,
        "local_clifford": block.local_diagnostics(),
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", required=True)
    parser.add_argument("--iterations", type=int, default=10)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--report-every", type=int, default=1)
    parser.add_argument("--seed", type=int, default=4)
    args = parser.parse_args()
    print(json.dumps(run(args)))


if __name__ == "__main__":
    main()
