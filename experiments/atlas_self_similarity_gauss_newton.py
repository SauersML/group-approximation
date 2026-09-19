"""Matrix-free Gauss--Newton solver for r(U)=iI in the 64D atlas block.

For a left tangent update U -> exp(X)U with X skew-Hermitian, every moving
factor F=U rho(g) U* has derivative [X,F].  The eight-letter survivor has four
such factors, so both the Jacobian and its real adjoint can be applied with a
small fixed number of dense matrix products.  SciPy LSMR solves the tangent
least-squares equation without materializing a 4096-square Jacobian.
"""

import argparse
import json
import math
import time

import numpy as np
from scipy.linalg import expm
from scipy.sparse.linalg import LinearOperator, lsmr


def unpack_hermitian(vector, dimension):
    matrix = np.zeros((dimension, dimension), dtype=np.complex128)
    matrix[np.diag_indices(dimension)] = vector[:dimension]
    cursor = dimension
    scale = math.sqrt(2.0)
    for row in range(dimension):
        for col in range(row + 1, dimension):
            real = vector[cursor] / scale
            imaginary = vector[cursor + 1] / scale
            cursor += 2
            matrix[row, col] = real + 1j * imaginary
            matrix[col, row] = real - 1j * imaginary
    return matrix


def pack_hermitian(matrix):
    dimension = matrix.shape[0]
    vector = np.empty(dimension * dimension, dtype=np.float64)
    vector[:dimension] = np.diag(matrix).real
    cursor = dimension
    scale = math.sqrt(2.0)
    for row in range(dimension):
        for col in range(row + 1, dimension):
            vector[cursor] = scale * matrix[row, col].real
            vector[cursor + 1] = scale * matrix[row, col].imag
            cursor += 2
    return vector


def pack_complex(matrix):
    return np.concatenate((matrix.real.reshape(-1), matrix.imag.reshape(-1)))


def unpack_complex(vector, dimension):
    size = dimension * dimension
    return (vector[:size].reshape(dimension, dimension)
            + 1j * vector[size:].reshape(dimension, dimension))


def relation_data(relative, factors, fixed_matrices):
    dimension = relative.shape[0]
    adjoint = relative.conj().T
    values = []
    for factor, matrix in zip(factors, fixed_matrices):
        values.append(matrix if factor == 1 else relative @ matrix @ adjoint)
    prefix = [np.eye(dimension, dtype=np.complex128)]
    for value in values:
        prefix.append(prefix[-1] @ value)
    suffix = [None] * (len(values) + 1)
    suffix[-1] = np.eye(dimension, dtype=np.complex128)
    for position in range(len(values) - 1, -1, -1):
        suffix[position] = values[position] @ suffix[position + 1]
    moving = [position for position, factor in enumerate(factors)
              if factor == 2]
    return prefix[-1], values, prefix, suffix, moving


def tangent_operator(values, prefix, suffix, moving):
    dimension = values[0].shape[0]
    domain = dimension * dimension
    codomain = 2 * domain

    def matvec(vector):
        hermitian = unpack_hermitian(vector, dimension)
        tangent = 1j * hermitian
        output = np.zeros((dimension, dimension), dtype=np.complex128)
        for position in moving:
            value = values[position]
            output += (prefix[position]
                       @ (tangent @ value - value @ tangent)
                       @ suffix[position + 1])
        return pack_complex(output)

    def rmatvec(vector):
        cotangent = unpack_complex(vector, dimension)
        gradient = np.zeros((dimension, dimension), dtype=np.complex128)
        for position in moving:
            value = values[position]
            left = prefix[position]
            right = suffix[position + 1]
            gradient += (left.conj().T @ cotangent
                         @ (value @ right).conj().T)
            gradient -= ((left @ value).conj().T @ cotangent
                         @ right.conj().T)
        hermitian_gradient = -1j * gradient
        hermitian_gradient = (
            hermitian_gradient + hermitian_gradient.conj().T) / 2
        return pack_hermitian(hermitian_gradient)

    return LinearOperator(
        (codomain, domain), matvec=matvec, rmatvec=rmatvec,
        dtype=np.float64)


def relation(relative, factors, fixed_matrices):
    return relation_data(relative, factors, fixed_matrices)[0]


def errors(value):
    dimension = value.shape[0]
    difference = value - 1j * np.eye(dimension)
    return {
        "hs_error": float(np.linalg.norm(difference) / math.sqrt(dimension)),
        "operator_error": float(np.linalg.norm(difference, 2)),
        "relation_trace": [
            float((np.trace(value) / dimension).real),
            float((np.trace(value) / dimension).imag),
        ],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--init", required=True)
    parser.add_argument("--bundle", required=True)
    parser.add_argument("--steps", type=int, default=4)
    parser.add_argument("--lsmr-iterations", type=int, default=200)
    parser.add_argument("--damp", type=float, default=1e-10)
    parser.add_argument("--save")
    args = parser.parse_args()
    relative = np.load(args.init)
    bundle = np.load(args.bundle)
    factors = bundle["factors"]
    fixed_matrices = bundle["matrices"]
    dimension = relative.shape[0]
    target = 1j * np.eye(dimension, dtype=np.complex128)
    started = time.time()

    for step_index in range(args.steps):
        value, values, prefix, suffix, moving = relation_data(
            relative, factors, fixed_matrices)
        operator = tangent_operator(values, prefix, suffix, moving)
        if step_index == 0:
            rng = np.random.default_rng(1729)
            domain_probe = rng.standard_normal(dimension * dimension)
            codomain_probe = rng.standard_normal(2 * dimension * dimension)
            left_inner = float(np.dot(
                operator.matvec(domain_probe), codomain_probe))
            right_inner = float(np.dot(
                domain_probe, operator.rmatvec(codomain_probe)))
            adjoint_error = abs(left_inner - right_inner) / max(
                1.0, abs(left_inner), abs(right_inner))
            if adjoint_error > 1e-11:
                raise AssertionError(
                    f"Jacobian adjoint check failed: {adjoint_error}")
        right_hand_side = -pack_complex(value - target)
        solution = lsmr(
            operator, right_hand_side,
            damp=args.damp, atol=1e-13, btol=1e-13,
            maxiter=args.lsmr_iterations)
        hermitian = unpack_hermitian(solution[0], dimension)
        old_error = errors(value)["hs_error"]
        accepted = False
        accepted_step_size = None
        for step_size in (1.0, 0.5, 0.25, 0.1, 0.03):
            candidate = expm(1j * step_size * hermitian) @ relative
            candidate_value = relation(candidate, factors, fixed_matrices)
            candidate_error = errors(candidate_value)["hs_error"]
            if candidate_error < old_error:
                relative = candidate
                value = candidate_value
                accepted = True
                accepted_step_size = step_size
                break
        record = {
            "event": "step",
            "step": step_index + 1,
            "elapsed_s": round(time.time() - started, 3),
            "adjoint_relative_error": adjoint_error,
            "lsmr_stop": int(solution[1]),
            "lsmr_iterations": int(solution[2]),
            "lsmr_residual_norm": float(solution[3]),
            "lsmr_condition_estimate": float(solution[6]),
            "tangent_norm": float(np.linalg.norm(hermitian)),
            "accepted": accepted,
            "accepted_step_size": accepted_step_size,
            **errors(value),
        }
        print(json.dumps(record), flush=True)
        if not accepted:
            break

    unitarity_error = np.linalg.norm(
        relative.conj().T @ relative - np.eye(dimension), 2)
    print(json.dumps({
        "event": "final",
        "elapsed_s": round(time.time() - started, 3),
        "unitarity_operator_error": float(unitarity_error),
        **errors(relation(relative, factors, fixed_matrices)),
    }), flush=True)
    if args.save:
        np.save(args.save, relative)


if __name__ == "__main__":
    main()
