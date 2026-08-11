"""Degree-one repair spectrum on finite SL(3,Z) presentation charts.

The fixed presentation uses the six elementary transvections, the Steinberg
relations, and the Conder--Robertson--Williams torsion relation.  It acts on
X_p = F_p^3 - {0} through reduction modulo p.  We construct the cellular
coboundaries d0 and d1 of the resulting finite presentation complex and
measure the bottom of the degree-one Hodge Laplacian

    Delta_1 = d1* d1 + d0 d0*.

Finite-index stabilizers in SL(3,Z) have property (T), hence no real H1.  A
uniform positive bottom is therefore the linear degree-one repair estimate
on this explicit family; decay would expose the obstructing cochain modes.
"""

import argparse
import itertools
import json
import time

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh


ROOTS = tuple((i, j) for i in range(3) for j in range(3) if i != j)


def transvection(i, j, prime):
    matrix = np.eye(3, dtype=np.int64)
    matrix[i, j] = 1
    return matrix % prime


def inverse_matrix(matrix, prime):
    # Every generator used here is I+E_ij with square-zero E_ij.
    inverse = np.eye(3, dtype=np.int64)
    positions = np.argwhere((matrix - inverse) % prime)
    if len(positions) != 1:
        raise ValueError("expected an elementary transvection")
    i, j = map(int, positions[0])
    inverse[i, j] = -1
    return inverse % prime


def inverse_word(word):
    return tuple((generator, -sign) for generator, sign in reversed(word))


def commutator(left, right):
    return left + right + inverse_word(left) + inverse_word(right)


def presentation_relators():
    root_index = {root: index for index, root in enumerate(ROOTS)}
    relators = []
    names = []

    for i, j, k in itertools.permutations(range(3)):
        left = ((root_index[(i, j)], 1),)
        right = ((root_index[(j, k)], 1),)
        target = ((root_index[(i, k)], -1),)
        relators.append(commutator(left, right) + target)
        names.append("steinberg_%d%d%d" % (i, j, k))

    for first, second in itertools.combinations(ROOTS, 2):
        i, j = first
        k, ell = second
        if i != ell and j != k:
            relators.append(commutator(
                ((root_index[first], 1),),
                ((root_index[second], 1),)))
            names.append("orth_%d%d_%d%d" % (i, j, k, ell))

    x12 = root_index[(0, 1)]
    x21 = root_index[(1, 0)]
    block = ((x12, 1), (x21, -1), (x12, 1))
    relators.append(block * 4)
    names.append("crw_torsion")
    return names, relators


def nonzero_vectors(prime):
    return np.array([vector for vector in itertools.product(range(prime),
                                                            repeat=3)
                     if any(vector)], dtype=np.int64)


def action_permutations(prime):
    vectors = nonzero_vectors(prime)
    index = {tuple(vector): position
             for position, vector in enumerate(vectors.tolist())}
    permutations = []
    inverse_permutations = []
    matrices = []
    for i, j in ROOTS:
        matrix = transvection(i, j, prime)
        inverse = inverse_matrix(matrix, prime)
        permutation = np.array(
            [index[tuple(((vector @ matrix) % prime).tolist())]
             for vector in vectors], dtype=np.int64)
        inverse_permutation = np.array(
            [index[tuple(((vector @ inverse) % prime).tolist())]
             for vector in vectors], dtype=np.int64)
        if not np.array_equal(permutation[inverse_permutation],
                              np.arange(len(vectors))):
            raise AssertionError("bad inverse permutation")
        matrices.append(matrix)
        permutations.append(permutation)
        inverse_permutations.append(inverse_permutation)
    return vectors, matrices, permutations, inverse_permutations


def validate_relators(prime, matrices, names, relators):
    identity = np.eye(3, dtype=np.int64) % prime
    for name, word in zip(names, relators):
        value = identity.copy()
        for generator, sign in word:
            factor = (matrices[generator] if sign == 1 else
                      inverse_matrix(matrices[generator], prime))
            value = (value @ factor) % prime
        if not np.array_equal(value, identity):
            raise AssertionError("invalid relation %s modulo %d" %
                                 (name, prime))


def coboundaries(prime):
    names, relators = presentation_relators()
    vectors, matrices, permutations, inverse_permutations = (
        action_permutations(prime))
    validate_relators(prime, matrices, names, relators)
    vertices = len(vectors)
    generators = len(ROOTS)
    edges = generators * vertices

    d0_rows = []
    d0_cols = []
    d0_data = []
    for generator, permutation in enumerate(permutations):
        for source, target in enumerate(permutation):
            edge = generator * vertices + source
            d0_rows.extend((edge, edge))
            d0_cols.extend((source, int(target)))
            d0_data.extend((-1.0, 1.0))
    d0 = coo_matrix((d0_data, (d0_rows, d0_cols)),
                    shape=(edges, vertices)).tocsr()

    d1_rows = []
    d1_cols = []
    d1_data = []
    cell = 0
    for word in relators:
        for start in range(vertices):
            current = start
            for generator, sign in word:
                if sign == 1:
                    source = current
                    current = int(permutations[generator][current])
                    coefficient = 1.0
                else:
                    source = int(inverse_permutations[generator][current])
                    current = source
                    coefficient = -1.0
                d1_rows.append(cell)
                d1_cols.append(generator * vertices + source)
                d1_data.append(coefficient)
            if current != start:
                raise AssertionError("relation path did not close")
            cell += 1
    d1 = coo_matrix((d1_data, (d1_rows, d1_cols)),
                    shape=(cell, edges)).tocsr()
    chain_error = d1 @ d0
    if chain_error.nnz and np.max(np.abs(chain_error.data)) > 1e-12:
        raise AssertionError("d1 d0 is nonzero")
    return names, vertices, d0, d1


def smallest_values(matrix, count):
    values = eigsh(matrix, k=count, which="SM", return_eigenvectors=False,
                   tol=1e-7, maxiter=500000)
    values.sort()
    return [float(value) for value in values]


def primitive_root(prime):
    factors = []
    value = prime - 1
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        factors.append(value)
    for candidate in range(2, prime):
        if all(pow(candidate, (prime - 1) // factor, prime) != 1
               for factor in factors):
            return candidate
    raise ValueError("no primitive root")


def low_mode_diagnostics(prime, d0, d1, laplacian1):
    values, vectors = eigsh(laplacian1, k=1, which="SM", tol=1e-8,
                            maxiter=500000)
    mode = vectors[:, 0]
    d1_energy = float(np.linalg.norm(d1 @ mode) ** 2)
    d0_energy = float(np.linalg.norm(d0.T @ mode) ** 2)

    points = nonzero_vectors(prime)
    point_index = {tuple(point): index
                   for index, point in enumerate(points.tolist())}
    scalar = primitive_root(prime)
    scalar_permutation = np.array(
        [point_index[tuple(((scalar * point) % prime).tolist())]
         for point in points], dtype=np.int64)
    shaped = mode.reshape((len(ROOTS), len(points)))
    translated = shaped.copy()
    correlations = []
    norm_squared = float(np.vdot(shaped, shaped).real)
    for _ in range(prime - 1):
        correlations.append(float(np.vdot(shaped, translated).real /
                                  norm_squared))
        translated = translated[:, scalar_permutation]
    weights = np.fft.fft(correlations).real / (prime - 1)
    top = np.argsort(weights)[-6:][::-1]
    return {
        "hodge_eigenvalue": float(values[0]),
        "d1_energy": d1_energy,
        "d0_adjoint_energy": d0_energy,
        "scalar_primitive_root": scalar,
        "top_scalar_characters": [
            [int(index), float(weights[int(index)])] for index in top
        ],
    }


def run(prime, eigenvalues, analyze):
    started = time.time()
    names, vertices, d0, d1 = coboundaries(prime)
    laplacian0 = d0.T @ d0
    laplacian1 = d1.T @ d1 + d0 @ d0.T
    graph_values = smallest_values(laplacian0, min(eigenvalues + 1,
                                                   vertices - 1))
    hodge_values = smallest_values(laplacian1, eigenvalues)
    result = {
        "prime": prime,
        "vertices": vertices,
        "generators": len(ROOTS),
        "relators": len(names),
        "edges": int(d0.shape[0]),
        "cells": int(d1.shape[0]),
        "d0_nnz": int(d0.nnz),
        "d1_nnz": int(d1.nnz),
        "graph_eigenvalues": graph_values,
        "hodge1_eigenvalues": hodge_values,
        "graph_sigma_positive": float(np.sqrt(max(0.0, graph_values[1]))),
        "hodge1_sigma_min": float(np.sqrt(max(0.0, hodge_values[0]))),
        "elapsed_s": round(time.time() - started, 3),
    }
    if analyze:
        result["low_mode"] = low_mode_diagnostics(
            prime, d0, d1, laplacian1)
        result["elapsed_s"] = round(time.time() - started, 3)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", type=int, nargs="+", default=(3, 5, 7, 11))
    parser.add_argument("--eigenvalues", type=int, default=4)
    parser.add_argument("--analyze", action="store_true")
    args = parser.parse_args()
    for prime in args.primes:
        print(json.dumps(run(prime, args.eigenvalues, args.analyze)),
              flush=True)


if __name__ == "__main__":
    main()
