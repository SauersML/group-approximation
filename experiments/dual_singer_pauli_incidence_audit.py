"""Audit every dual Singer incidence on one three-bit Pauli register.

Run on MSI only.  The calculation enumerates GL_3(F_2), selects every
order-seven element, and verifies that every nonzero primal/dual orbit is
the full seven-point set.  Consequently every cross-commutator incidence
row and column has weight four, even after a second Singer action is added.
"""

from itertools import product


VECTORS = tuple(range(8))
NONZERO = tuple(range(1, 8))


def parity(value):
    return value.bit_count() & 1


def apply(matrix, vector):
    result = 0
    for row, row_mask in enumerate(matrix):
        result |= parity(row_mask & vector) << row
    return result


def multiply(left, right):
    columns = tuple(
        sum(((right[row] >> column) & 1) << row for row in range(3))
        for column in range(3)
    )
    return tuple(
        sum(parity(left[row] & columns[column]) << column
            for column in range(3))
        for row in range(3)
    )


IDENTITY = (1, 2, 4)


def power(matrix, exponent):
    result = IDENTITY
    for _ in range(exponent):
        result = multiply(result, matrix)
    return result


def transpose(matrix):
    return tuple(
        sum(((matrix[row] >> column) & 1) << row for row in range(3))
        for column in range(3)
    )


def inverse(matrix):
    for candidate in GL3:
        if multiply(matrix, candidate) == multiply(candidate, matrix) == IDENTITY:
            return candidate
    raise AssertionError("matrix is not invertible")


def orbit(matrix, vector):
    answer = []
    current = vector
    for _ in range(7):
        answer.append(current)
        current = apply(matrix, current)
    return tuple(answer)


def pairing(functional, vector):
    return parity(functional & vector)


GL3 = tuple(
    matrix
    for matrix in product(VECTORS, repeat=3)
    if len({apply(matrix, vector) for vector in VECTORS}) == 8
)


def main():
    assert len(GL3) == 168
    singers = tuple(
        matrix for matrix in GL3
        if power(matrix, 7) == IDENTITY and matrix != IDENTITY
    )
    assert len(singers) == 48

    tables = set()
    for singer in singers:
        dual = transpose(inverse(singer))
        for primal in NONZERO:
            primal_orbit = orbit(singer, primal)
            assert set(primal_orbit) == set(NONZERO)
            assert not __import__("functools").reduce(int.__xor__, primal_orbit)
            for functional in NONZERO:
                dual_orbit = orbit(dual, functional)
                assert set(dual_orbit) == set(NONZERO)
                assert not __import__("functools").reduce(int.__xor__, dual_orbit)
                table = tuple(
                    tuple(pairing(phi, vector) for phi in dual_orbit)
                    for vector in primal_orbit
                )
                assert all(sum(row) == 4 for row in table)
                assert all(sum(table[row][column] for row in range(7)) == 4
                           for column in range(7))
                assert sum(sum(row) for row in table) == 28
                tables.add(table)

    # A second Singer element acts on the same Pauli space by another
    # permutation implementer.  The ordered pair introduces no new label
    # vectors: both primal and dual orbits remain V\{0}.
    for first in singers:
        for second in singers:
            for vector in NONZERO:
                assert set(orbit(first, vector)) == set(orbit(second, vector))

    print("GL3 size", len(GL3))
    print("order-seven elements", len(singers))
    print("distinct ordered incidence tables", len(tables))
    print("every Singer row/column weight 4; total cross exponent 28")
    print("every dual Singer orbit is only a reordering of the same Pauli register")


if __name__ == "__main__":
    main()
