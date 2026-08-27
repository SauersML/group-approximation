#!/usr/bin/env python3
"""Find and verify low-arity invertible-direction Schur compilers over F_2.

For k selector bits, search in GF(2^(2^k)) for an affine map

    a(x) = a0 + sum_i x_i b_i

such that the 2^k vectors a(x)^(-1) form an F_2-basis.  Multiplication by
a(x) is then an always-invertible affine matrix U(x), every directional
coefficient multiplication-by-b_i is invertible, and every Boolean truth
table is a linear functional of U(x)^(-1) 1.  The bordered Schur matrix

    [[U(x), 1], [ell_f, 0]]

therefore has rank 2^k + f(x).

The script uses only exact integer arithmetic and the Python standard library.
It emits explicit replayable certificates for arities one through four.
"""

from __future__ import annotations

import json
import random
from itertools import product


KNOWN_MODULI = {
    2: 0b111,          # x^2 + x + 1
    4: 0b10011,        # x^4 + x + 1
    8: 0x11B,          # x^8 + x^4 + x^3 + x + 1
    16: 0x1100B,       # x^16 + x^12 + x^3 + x + 1
}


def poly_degree(a: int) -> int:
    return a.bit_length() - 1


def poly_mod(a: int, modulus: int) -> int:
    degree = poly_degree(modulus)
    while a and poly_degree(a) >= degree:
        a ^= modulus << (poly_degree(a) - degree)
    return a


def is_irreducible(modulus: int, degree: int) -> bool:
    if poly_degree(modulus) != degree or not (modulus & 1):
        return False
    for divisor_degree in range(1, degree // 2 + 1):
        start = (1 << divisor_degree) | 1
        stop = 1 << (divisor_degree + 1)
        for divisor in range(start, stop, 2):
            if poly_degree(divisor) != divisor_degree:
                continue
            if poly_mod(modulus, divisor) == 0:
                return False
    return True


def gf_mul(a: int, b: int, modulus: int, degree: int) -> int:
    out = 0
    top = 1 << degree
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & top:
            a ^= modulus
    return out & (top - 1)


def gf_pow(a: int, exponent: int, modulus: int, degree: int) -> int:
    out = 1
    while exponent:
        if exponent & 1:
            out = gf_mul(out, a, modulus, degree)
        a = gf_mul(a, a, modulus, degree)
        exponent >>= 1
    return out


def gf_inv(a: int, modulus: int, degree: int) -> int:
    if not a:
        raise ZeroDivisionError
    return gf_pow(a, (1 << degree) - 2, modulus, degree)


def rank_bits(rows: list[int], width: int) -> int:
    rows = rows[:]
    rank = 0
    for column in range(width):
        pivot = next(
            (index for index in range(rank, len(rows))
             if (rows[index] >> column) & 1),
            None,
        )
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for index in range(len(rows)):
            if index != rank and ((rows[index] >> column) & 1):
                rows[index] ^= rows[rank]
        rank += 1
    return rank


def multiplication_matrix(a: int, modulus: int, degree: int) -> list[list[int]]:
    columns = [gf_mul(a, 1 << column, modulus, degree)
               for column in range(degree)]
    return [
        [(columns[column] >> row) & 1 for column in range(degree)]
        for row in range(degree)
    ]


def rank_matrix(matrix: list[list[int]]) -> int:
    rows = [sum(bit << column for column, bit in enumerate(row))
            for row in matrix]
    return rank_bits(rows, len(matrix[0]) if matrix else 0)


def affine_values(a0: int, directions: list[int]) -> list[int]:
    values = []
    for x in product((0, 1), repeat=len(directions)):
        value = a0
        for bit, direction in zip(x, directions):
            if bit:
                value ^= direction
        values.append(value)
    return values


def search_certificate(k: int, seed: int = 20260820) -> dict:
    degree = 1 << k
    modulus = KNOWN_MODULI[degree]
    assert is_irreducible(modulus, degree)
    rng = random.Random(seed + k)
    trials = 0
    while True:
        trials += 1
        directions = [rng.randrange(1, 1 << degree) for _ in range(k)]
        if rank_bits(directions, degree) != k:
            continue
        a0 = rng.randrange(1, 1 << degree)
        values = affine_values(a0, directions)
        if 0 in values or len(set(values)) != len(values):
            continue
        inverses = [gf_inv(value, modulus, degree) for value in values]
        if rank_bits(inverses, degree) == degree:
            break
        if trials >= 1_000_000:
            raise RuntimeError(f"no certificate found for k={k}")

    # Every linear functional ell gives one truth table.  Since the reciprocal
    # vectors are a basis, these must exhaust all 2^(2^k) predicates.  Replay
    # this bijectivity directly instead of merely counting dimensions.
    truth_tables = {
        sum(((ell & inverse).bit_count() & 1) << index
            for index, inverse in enumerate(inverses))
        for ell in range(1 << degree)
    }
    assert len(truth_tables) == 1 << degree

    coefficient_ranks = [
        rank_matrix(multiplication_matrix(direction, modulus, degree))
        for direction in directions
    ]
    value_ranks = [
        rank_matrix(multiplication_matrix(value, modulus, degree))
        for value in values
    ]
    assert coefficient_ranks == [degree] * k
    assert value_ranks == [degree] * (1 << k)

    return {
        "arity": k,
        "matrix_size": degree,
        "modulus_hex": hex(modulus),
        "a0_hex": hex(a0),
        "directions_hex": [hex(value) for value in directions],
        "affine_values_hex": [hex(value) for value in values],
        "reciprocals_hex": [hex(value) for value in inverses],
        "reciprocal_rank": rank_bits(inverses, degree),
        "coefficient_ranks": coefficient_ranks,
        "value_ranks": value_ranks,
        "predicates_certified": len(truth_tables),
        "search_trials": trials,
    }


def verify_two_copy_reset(certificate: dict) -> dict:
    """Verify that every bit derivative gives a full-rank reset spin form."""
    degree = certificate["matrix_size"]
    modulus = int(certificate["modulus_hex"], 16)
    directions = [int(value, 16)
                  for value in certificate["directions_hex"]]
    ranks = []
    for direction in directions:
        derivative = multiplication_matrix(direction, modulus, degree)
        ranks.append(rank_matrix(derivative))
    assert ranks == [degree] * len(directions)
    return {
        "derivative_ranks": ranks,
        "baseline_spin_dimension": 1 << degree,
        "reset_spin_dimensions": [1 << rank for rank in ranks],
        "scale_preserved": all(rank == degree for rank in ranks),
    }


def main() -> None:
    records = []
    for k in range(1, 5):
        certificate = search_certificate(k)
        certificate["two_copy_reset"] = verify_two_copy_reset(certificate)
        records.append(certificate)
    print(json.dumps({"all_checks_pass": True, "records": records}, indent=2))


if __name__ == "__main__":
    main()
