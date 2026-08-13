"""Scalar-character blocks of the SL(3,Z) degree-one Hodge operator.

The scalar F_p^* action on X_p=F_p^3-{0} commutes with every generator in
sl3_degree_one_spectrum.py.  Fourier transform along each scalar orbit
decomposes the full complex into p-1 blocks over P^2(F_p).  This program
constructs a block from exact projective transitions and integer exponents
modulo p-1; floating-point roots of unity enter only when the selected
character is evaluated.

This reduces C^1 from 6(p^3-1) coordinates to 6(p^2+p+1) coordinates and
identifies the precise character sector in which a low mode occurs.
"""

import argparse
import json
import time

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh

from sl3_degree_one_spectrum import (
    ROOTS,
    inverse_matrix,
    presentation_relators,
    primitive_root,
    transvection,
    validate_relators,
)


def projective_points(prime):
    """Canonical representatives: first nonzero coordinate is one."""
    points = []
    for pivot in range(3):
        prefix = (0,) * pivot + (1,)
        tail_length = 2 - pivot
        for tail_number in range(prime ** tail_length):
            tail = []
            value = tail_number
            for _ in range(tail_length):
                tail.append(value % prime)
                value //= prime
            points.append(prefix + tuple(tail))
    return np.asarray(points, dtype=np.int64)


def discrete_log_table(prime):
    generator = primitive_root(prime)
    table = {}
    value = 1
    for exponent in range(prime - 1):
        table[value] = exponent
        value = (value * generator) % prime
    if len(table) != prime - 1:
        raise AssertionError("primitive root did not enumerate F_p^*")
    return generator, table


def normalize_projective(vector, prime, logarithms):
    for coordinate in vector:
        scalar = int(coordinate) % prime
        if scalar:
            inverse = pow(scalar, prime - 2, prime)
            representative = tuple(
                int((inverse * entry) % prime) for entry in vector)
            return representative, logarithms[scalar]
    raise AssertionError("zero vector has no projective normalization")


def transition_tables(prime):
    names, relators = presentation_relators()
    points = projective_points(prime)
    point_index = {tuple(point): index
                   for index, point in enumerate(points.tolist())}
    scalar_generator, logarithms = discrete_log_table(prime)
    matrices = [transvection(i, j, prime) for i, j in ROOTS]
    validate_relators(prime, matrices, names, relators)

    targets = np.empty((2, len(ROOTS), len(points)), dtype=np.int64)
    exponents = np.empty_like(targets)
    for sign_index, sign in enumerate((1, -1)):
        for generator, matrix in enumerate(matrices):
            acting = matrix if sign == 1 else inverse_matrix(matrix, prime)
            for source, point in enumerate(points):
                image = (point @ acting) % prime
                representative, exponent = normalize_projective(
                    image, prime, logarithms)
                targets[sign_index, generator, source] = (
                    point_index[representative])
                exponents[sign_index, generator, source] = exponent
    return (names, relators, points, scalar_generator, targets, exponents)


def exact_block_pattern(prime):
    """Return sparse positions, signs, and scalar exponents for d0 and d1."""
    (names, relators, points, scalar_generator, targets, exponents) = (
        transition_tables(prime))
    vertices = len(points)
    edges = len(ROOTS) * vertices

    d0_rows = []
    d0_cols = []
    d0_signs = []
    d0_exponents = []
    for generator in range(len(ROOTS)):
        for source in range(vertices):
            edge = generator * vertices + source
            d0_rows.extend((edge, edge))
            d0_cols.extend((source, int(targets[0, generator, source])))
            d0_signs.extend((-1, 1))
            d0_exponents.extend((0, int(exponents[0, generator, source])))

    d1_rows = []
    d1_cols = []
    d1_signs = []
    d1_exponents = []
    cell = 0
    modulus = prime - 1
    for word in relators:
        for start in range(vertices):
            current = start
            scalar_exponent = 0
            for generator, sign in word:
                if sign == 1:
                    edge_source = current
                    edge_exponent = scalar_exponent
                    current_exponent = int(exponents[0, generator, current])
                    current = int(targets[0, generator, current])
                    scalar_exponent = (
                        scalar_exponent + current_exponent) % modulus
                    coefficient = 1
                else:
                    inverse_exponent = int(exponents[1, generator, current])
                    current = int(targets[1, generator, current])
                    scalar_exponent = (
                        scalar_exponent + inverse_exponent) % modulus
                    edge_source = current
                    edge_exponent = scalar_exponent
                    coefficient = -1
                d1_rows.append(cell)
                d1_cols.append(generator * vertices + edge_source)
                d1_signs.append(coefficient)
                d1_exponents.append(edge_exponent)
            if current != start or scalar_exponent != 0:
                raise AssertionError("projective relation path did not close")
            cell += 1

    return {
        "prime": prime,
        "scalar_generator": scalar_generator,
        "vertices": vertices,
        "generators": len(ROOTS),
        "relators": len(names),
        "relator_names": names,
        "edges": edges,
        "cells": cell,
        "d0": (np.asarray(d0_rows), np.asarray(d0_cols),
               np.asarray(d0_signs), np.asarray(d0_exponents)),
        "d1": (np.asarray(d1_rows), np.asarray(d1_cols),
               np.asarray(d1_signs), np.asarray(d1_exponents)),
    }


def evaluate_pattern(entries, shape, character, modulus):
    rows, columns, signs, exponents = entries
    phases = np.exp((2j * np.pi * character / modulus) * exponents)
    matrix = coo_matrix((signs * phases, (rows, columns)), shape=shape)
    matrix.sum_duplicates()
    return matrix.tocsr()


def character_block(pattern, character):
    modulus = pattern["prime"] - 1
    d0 = evaluate_pattern(
        pattern["d0"], (pattern["edges"], pattern["vertices"]),
        character, modulus)
    d1 = evaluate_pattern(
        pattern["d1"], (pattern["cells"], pattern["edges"]),
        character, modulus)
    chain = d1 @ d0
    chain_error = (float(np.max(np.abs(chain.data)))
                   if chain.nnz else 0.0)
    if chain_error > 1e-10:
        raise AssertionError("character block has d1 d0 error %g" %
                             chain_error)
    return d0, d1, chain_error


def structure_diagnostics(pattern, mode, d0, d1):
    vertices = pattern["vertices"]
    shaped = mode.reshape((pattern["generators"], vertices))
    defects = (d1 @ mode).reshape((pattern["relators"], vertices))
    gram = shaped @ shaped.conjugate().T
    points = projective_points(pattern["prime"])
    zero_masks = ((points == 0) * np.array((1, 2, 4))).sum(axis=1)
    point_energy = np.sum(np.abs(shaped) ** 2, axis=0)
    return {
        "inverse_participation_ratio": float(np.sum(np.abs(mode) ** 4)),
        "max_coordinate_squared": float(np.max(np.abs(mode) ** 2)),
        "generator_energy": [
            float(value) for value in np.sum(np.abs(shaped) ** 2, axis=1)
        ],
        "generator_gram": [
            [[float(value.real), float(value.imag)] for value in row]
            for row in gram
        ],
        "relator_defect_energy": [
            [name, float(value)] for name, value in zip(
                pattern["relator_names"],
                np.sum(np.abs(defects) ** 2, axis=1))
        ],
        "point_zero_mask_energy": [
            [int(mask), float(np.sum(point_energy[zero_masks == mask]))]
            for mask in sorted(set(zero_masks.tolist()))
        ],
        "d0_adjoint_norm": float(np.linalg.norm(d0.conjugate().T @ mode)),
    }


def analyze_character(pattern, character, eigenvalues, structure):
    started = time.time()
    d0, d1, chain_error = character_block(pattern, character)
    laplacian = d1.conjugate().T @ d1 + d0 @ d0.conjugate().T
    count = min(eigenvalues, laplacian.shape[0] - 1)
    # Delta_1 is positive semidefinite.  Asking ARPACK for smallest algebraic
    # eigenvalues is materially more stable on complex character blocks than
    # the generic smallest-magnitude mode (notably for the p=3 sign block).
    values, vectors = eigsh(laplacian, k=count, which="SA", tol=1e-9,
                            maxiter=500000)
    order = np.argsort(values)
    values = values[order]
    mode = vectors[:, order[0]]
    residual = np.linalg.norm(laplacian @ mode - values[0] * mode)
    result = {
        "character": character,
        "conjugate_character": (-character) % (pattern["prime"] - 1),
        "hodge1_eigenvalues": [float(value) for value in values],
        "hodge1_sigma_min": float(np.sqrt(max(0.0, values[0]))),
        "d1_energy": float(np.linalg.norm(d1 @ mode) ** 2),
        "d0_adjoint_energy": float(np.linalg.norm(d0.conjugate().T @ mode) ** 2),
        "eigen_residual": float(residual),
        "chain_error": chain_error,
        "elapsed_s": round(time.time() - started, 3),
    }
    if structure:
        result["structure"] = structure_diagnostics(
            pattern, mode, d0, d1)
        result["elapsed_s"] = round(time.time() - started, 3)
    return result


def run(prime, characters, eigenvalues, structure):
    started = time.time()
    pattern = exact_block_pattern(prime)
    modulus = prime - 1
    selected = list(range(modulus)) if characters is None else characters
    if any(character < 0 or character >= modulus for character in selected):
        raise ValueError("characters must lie in [0,p-2]")
    result = {key: value for key, value in pattern.items()
              if key not in ("d0", "d1")}
    result["pattern_d0_terms"] = int(len(pattern["d0"][0]))
    result["pattern_d1_terms"] = int(len(pattern["d1"][0]))
    result["characters"] = [
        analyze_character(pattern, character, eigenvalues, structure)
        for character in selected
    ]
    result["elapsed_s"] = round(time.time() - started, 3)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", type=int, nargs="+", required=True)
    parser.add_argument("--characters", type=int, nargs="+")
    parser.add_argument("--eigenvalues", type=int, default=2)
    parser.add_argument("--structure", action="store_true")
    args = parser.parse_args()
    for prime in args.primes:
        print(json.dumps(run(prime, args.characters, args.eigenvalues,
                             args.structure)),
              flush=True)


if __name__ == "__main__":
    main()
