#!/usr/bin/env python3
"""Exact rational certificate for the Atlas ASC coercivity constant 1/14.

This script rebuilds the two elements W_pkt,W_cov of Z[A8] from the 234
literal first-boundary words, constructs rational Young-seminormal models for
one partition in every conjugate pair of partitions of 8, and verifies

                    W_pkt - 14 W_cov >= 0

in every irreducible A8 representation.  Self-conjugate S8 representations
may split on A8, but positivity on their full restriction checks both summands.
No floating point, SDP solver, Sage, GAP, or unrecorded generated file is used.
"""

from __future__ import annotations

import hashlib
import json
import os
import sys
from collections import Counter, deque
from fractions import Fraction
from math import gcd
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
if (HERE / "atlas_asc_packet_build.py").exists():
    # Canonical location after promotion to group-approximation/experiments.
    EXPERIMENTS = HERE
    REPO = HERE.parent
else:
    # Isolated agent workspace requested for this task.
    REPO = HERE.parent / "group-approximation"
    EXPERIMENTS = REPO / "experiments"
sys.path.insert(0, str(EXPERIMENTS))

from atlas_asc_packet_build import merge, raw_s3_letters  # noqa: E402
from atlas_boundary_amalgam_normal_form import transported_word  # noqa: E402
from atlas_boundary_group_algebra_audit import matrix_from_key  # noqa: E402
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX  # noqa: E402
from atlas_certified_a8_alignment import boundary_words  # noqa: E402
from atlas_certified_dual_number_certificate import natural_a8_map  # noqa: E402
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key  # noqa: E402


Q = Fraction


def lcm(a: int, b: int) -> int:
    return abs(a // gcd(a, b) * b) if a and b else 0


def partitions(n: int, ceiling: int | None = None):
    if n == 0:
        yield ()
        return
    ceiling = n if ceiling is None else min(n, ceiling)
    for first in range(ceiling, 0, -1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


def conjugate_partition(shape):
    return tuple(sum(row > column for row in shape)
                 for column in range(max(shape)))


def selected_partitions():
    selected, seen = [], set()
    for shape in partitions(8):
        other = conjugate_partition(shape)
        if shape in seen:
            continue
        seen.update((shape, other))
        selected.append(shape)
    return selected


def standard_tableaux(shape):
    """Positions of 1,...,8 for all standard tableaux of ``shape``."""
    out = []

    def rec(rows, label, reverse_positions):
        if label == 0:
            out.append(tuple(reversed(reverse_positions)))
            return
        for row, length in enumerate(rows):
            if length and (row + 1 == len(rows) or rows[row + 1] < length):
                nxt = list(rows)
                column = nxt[row] - 1
                nxt[row] -= 1
                rec(tuple(nxt), label - 1,
                    reverse_positions + ((row, column),))

    rec(tuple(shape), sum(shape), ())
    return out


def identity(n):
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def add_scaled(out, matrix, coefficient):
    if not coefficient:
        return
    for row_out, row in zip(out, matrix):
        for column, value in enumerate(row):
            if value:
                row_out[column] += coefficient * value


def matvec(a, vector):
    return [sum((entry * value for entry, value in zip(row, vector)), Q(0))
            for row in a]


def verify_coxeter(generators):
    """Check the exact S8 Coxeter presentation on the seminormal matrices."""
    dimension = len(generators[0])
    basis = [[Q(i == j) for i in range(dimension)] for j in range(dimension)]
    sparse_columns = [[
        [(row, operator[row][column]) for row in range(dimension)
         if operator[row][column]]
        for column in range(dimension)
    ] for operator in generators]

    def act(word, vector):
        for label in reversed(word):
            out = [Q(0)] * dimension
            for column, source in enumerate(vector):
                if source:
                    for row, coefficient in sparse_columns[label][column]:
                        out[row] += coefficient * source
            vector = out
        return vector

    for vector in basis:
        for i in range(7):
            if act((i, i), vector) != vector:
                raise AssertionError("seminormal generator is not involutive")
        for i in range(6):
            if act((i, i + 1, i), vector) != act((i + 1, i, i + 1), vector):
                raise AssertionError("seminormal braid relation failed")
        for i in range(7):
            for j in range(i + 2, 7):
                if act((i, j), vector) != act((j, i), vector):
                    raise AssertionError("seminormal distant commutation failed")


def adjacent_generators(shape):
    """Rational Young seminormal matrices and their invariant diagonal form."""
    tableaux = standard_tableaux(shape)
    index = {tableau: position for position, tableau in enumerate(tableaux)}
    dimension = len(tableaux)
    generators = []
    weight_edges = []
    for label in range(1, 8):
        operator = [[Q(0) for _ in range(dimension)]
                    for _ in range(dimension)]
        seen = set()
        for position, tableau in enumerate(tableaux):
            if position in seen:
                continue
            before, after = tableau[label - 1], tableau[label]
            axial = ((after[1] - after[0]) - (before[1] - before[0]))
            if before[0] == after[0] or before[1] == after[1]:
                operator[position][position] = Q(
                    1 if before[0] == after[0] else -1)
                seen.add(position)
                continue
            swapped = list(tableau)
            swapped[label - 1], swapped[label] = swapped[label], swapped[label - 1]
            partner = index[tuple(swapped)]
            if before[0] < after[0]:
                high, low, r = position, partner, axial
            else:
                high, low, r = partner, position, -axial
            q = Q(1) - Q(1, r * r)
            operator[high][high] = Q(1, r)
            operator[low][high] = Q(1)
            operator[high][low] = q
            operator[low][low] = Q(-1, r)
            weight_edges.append((high, low, q))
            seen.update((high, low))
        generators.append(operator)

    # G S_i = S_i^T G.  The tableau graph is connected in each Specht module.
    weights = [None] * dimension
    weights[0] = Q(1)
    queue = deque([0])
    adjacency = [[] for _ in range(dimension)]
    for high, low, ratio in weight_edges:
        adjacency[high].append((low, ratio))
        adjacency[low].append((high, Q(1) / ratio))
    while queue:
        source = queue.popleft()
        for target, ratio in adjacency[source]:
            candidate = weights[source] * ratio
            if weights[target] is None:
                weights[target] = candidate
                queue.append(target)
            elif weights[target] != candidate:
                raise AssertionError("inconsistent seminormal Gram weights")
    if any(value is None or value <= 0 for value in weights):
        raise AssertionError("seminormal Gram form is not positive")
    for operator in generators:
        for i in range(dimension):
            for j in range(dimension):
                if weights[i] * operator[i][j] != weights[j] * operator[j][i]:
                    raise AssertionError("seminormal generator not G-self-adjoint")
    verify_coxeter(generators)
    return generators, weights


def adjacent_factorization(permutation):
    """Factors p=s_k...s_1 in the usual functional composition convention."""
    values = list(permutation)
    reductions = []
    while True:
        pivot = next((i for i in range(7) if values[i] > values[i + 1]), None)
        if pivot is None:
            break
        values[pivot], values[pivot + 1] = values[pivot + 1], values[pivot]
        reductions.append(pivot)
    if values != list(range(8)):
        raise AssertionError("not a permutation")
    return list(reversed(reductions))


def right_multiply_adjacent(matrix, generator):
    """Dense-by-two-sparse exact multiplication."""
    dimension = len(matrix)
    out = [[Q(0) for _ in range(dimension)] for _ in range(dimension)]
    nonzero_columns = [
        [(row, generator[row][column]) for row in range(dimension)
         if generator[row][column]]
        for column in range(dimension)
    ]
    for row in range(dimension):
        for column, entries in enumerate(nonzero_columns):
            out[row][column] = sum(
                (matrix[row][source] * value for source, value in entries), Q(0))
    return out


def representation(permutation, generators):
    out = identity(len(generators[0]))
    for label in adjacent_factorization(permutation):
        out = right_multiply_adjacent(out, generators[label])
    return out


def packet_elements():
    """Rebuild W_pkt, W_cov, and A=W_pkt-14 W_cov in Z[A8]."""
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    vectors = []
    elements = {}
    for raw in boundary_words():
        word = merge(transported_word(raw, alignment, alignment_inverse))
        prefix = I4.copy()
        vector = Counter()
        for factor, matrix in word:
            image = gf2_mul(prefix, matrix)
            if factor == 2:
                before, after = matrix_key(prefix), matrix_key(image)
                elements[before] = prefix.copy()
                elements[after] = image.copy()
                vector[before] += 1
                vector[after] -= 1
            prefix = image
        if not np.array_equal(prefix, I4):
            raise AssertionError("boundary word is not fold-trivial")
        vectors.append({key: value for key, value in vector.items() if value})

    packet = Counter()
    for vector in vectors:
        items = [(elements[key], value) for key, value in vector.items()]
        for left, coefficient_left in items:
            inverse = gf2_inv(left)
            for right, coefficient_right in items:
                packet[matrix_key(gf2_mul(inverse, right))] += (
                    coefficient_left * coefficient_right)

    covariance = Counter({matrix_key(I4): 4})
    letters, _raw = raw_s3_letters(alignment, alignment_inverse)
    for letter in letters:
        covariance[matrix_key(letter)] -= 2
    certificate = packet.copy()
    for key, coefficient in covariance.items():
        certificate[key] -= 14 * coefficient
    certificate = Counter({key: value for key, value in certificate.items() if value})
    if (len(vectors), len(packet), packet[matrix_key(I4)], sum(packet.values())) != (
            234, 101, 1516, 0):
        raise AssertionError("authoritative packet fingerprint changed")
    return packet, covariance, certificate


def permutation_table():
    # This independently rebuilds all 20,160 images from the six fixed
    # exceptional-isomorphism generator pairs and checks bijectivity.
    raw = natural_a8_map()
    return {bytes.fromhex(key): tuple(permutation)
            for key, permutation in raw.items()}


def represented_element(coefficients, permutations, generators):
    dimension = len(generators[0])
    out = [[Q(0) for _ in range(dimension)] for _ in range(dimension)]
    for key, coefficient in sorted(coefficients.items(), key=lambda item: item[0]):
        add_scaled(out, representation(permutations[key], generators), Q(coefficient))
    return out


def gram_symmetrize(operator, weights):
    out = [[weights[i] * operator[i][j] for j in range(len(operator))]
           for i in range(len(operator))]
    if out != transpose(out):
        raise AssertionError("self-adjoint group-algebra element lost symmetry")
    return out


def psd_ldl(matrix):
    """Exact symmetric elimination; returns positive pivots and nullity."""
    work = [row[:] for row in matrix]
    dimension = len(work)
    pivots = []
    active = list(range(dimension))
    while active:
        pivot_position = next((position for position, index in enumerate(active)
                               if work[index][index] > 0), None)
        if pivot_position is None:
            if any(work[i][i] < 0 for i in active):
                return False, pivots, None
            if any(work[i][j] for i in active for j in active):
                return False, pivots, None
            return True, pivots, len(active)
        active[0], active[pivot_position] = active[pivot_position], active[0]
        pivot = active.pop(0)
        value = work[pivot][pivot]
        pivots.append(value)
        for offset, i in enumerate(active):
            for j in active[offset:]:
                updated = work[i][j] - work[i][pivot] * work[pivot][j] / value
                work[i][j] = updated
                work[j][i] = updated
        for i in active:
            work[i][pivot] = work[pivot][i] = Q(0)
    return True, pivots, 0


def kernel_basis(matrix):
    """Exact right-nullspace basis by Gauss-Jordan elimination."""
    work = [row[:] for row in matrix]
    row_count = len(work)
    column_count = len(work[0]) if work else 0
    pivot_columns = []
    row = 0
    for column in range(column_count):
        pivot = next((i for i in range(row, row_count) if work[i][column]), None)
        if pivot is None:
            continue
        work[row], work[pivot] = work[pivot], work[row]
        scale = work[row][column]
        work[row] = [value / scale for value in work[row]]
        for i in range(row_count):
            if i != row and work[i][column]:
                factor = work[i][column]
                work[i] = [left - factor * right
                           for left, right in zip(work[i], work[row])]
        pivot_columns.append(column)
        row += 1
        if row == row_count:
            break
    free = [column for column in range(column_count) if column not in pivot_columns]
    basis = []
    for column in free:
        vector = [Q(0)] * column_count
        vector[column] = Q(1)
        for pivot_row, pivot_column in enumerate(pivot_columns):
            vector[pivot_column] = -work[pivot_row][column]
        basis.append(vector)
    return basis


def rational_fingerprint(matrix):
    digest = hashlib.sha256()
    for row in matrix:
        for value in row:
            digest.update(f"{value.numerator}/{value.denominator};".encode())
    return digest.hexdigest()


def main():
    packet, covariance, certificate = packet_elements()
    permutations = permutation_table()
    missing = (set(packet) | set(covariance)) - set(permutations)
    if missing:
        raise AssertionError(f"natural A8 table misses {len(missing)} elements")

    records = []
    sharp_somewhere = False
    for shape in selected_partitions():
        generators, weights = adjacent_generators(shape)
        a_operator = represented_element(certificate, permutations, generators)
        c_operator = represented_element(covariance, permutations, generators)
        a_form = gram_symmetrize(a_operator, weights)
        c_form = gram_symmetrize(c_operator, weights)
        a_psd, a_pivots, a_nullity = psd_ldl(a_form)
        c_psd, _c_pivots, _c_nullity = psd_ldl(c_form)
        if not a_psd or not c_psd:
            raise AssertionError(f"exact positivity failed in partition {shape}")
        kernel = kernel_basis(a_operator)
        if len(kernel) != a_nullity:
            raise AssertionError("LDL and nullspace dimensions disagree")
        equality_nonzero = any(any(matvec(c_operator, vector)) for vector in kernel)
        sharp_somewhere |= equality_nonzero
        records.append({
            "partition": list(shape),
            "dimension": len(a_operator),
            "certificate_rank": len(a_operator) - len(kernel),
            "certificate_nullity": len(kernel),
            "positive_ldl_pivots": len(a_pivots),
            "equality_has_positive_covariance": equality_nonzero,
            "form_sha256": rational_fingerprint(a_form),
            "max_numerator_bits": max((abs(value.numerator).bit_length()
                                       for row in a_form for value in row), default=0),
            "max_denominator_bits": max((value.denominator.bit_length()
                                         for row in a_form for value in row), default=0),
        })
    if not sharp_somewhere:
        raise AssertionError("1/14 verified only as a non-sharp upper bound")

    coefficient_bytes = json.dumps(
        sorted((key.hex(), value) for key, value in certificate.items()),
        separators=(",", ":"),
    ).encode()
    report = {
        "arithmetic": "exact fractions.Fraction over Q",
        "group": "GL(4,2) ~= A8",
        "group_order": 20160,
        "boundary_words": 234,
        "support_W_pkt": len(packet),
        "support_W_cov": len(covariance),
        "support_W_pkt_minus_14_W_cov": len(certificate),
        "trace_W_pkt": packet[matrix_key(I4)],
        "coefficient_sum_W_pkt": sum(packet.values()),
        "certificate_coefficient_sha256": hashlib.sha256(coefficient_bytes).hexdigest(),
        "selected_S8_partitions": len(records),
        "covers_every_A8_irrep": True,
        "W_pkt_minus_14_W_cov_positive_in_every_sector": True,
        "one_fourteenth_is_attained": True,
        "records": records,
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
