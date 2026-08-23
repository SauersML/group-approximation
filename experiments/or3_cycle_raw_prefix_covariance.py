#!/usr/bin/env python3
"""Exact seven-dimensional witness for the OR3 raw-prefix covariance gate.

The three OR3 contexts form the Berge triangle

    c1 -- x12 -- c2 -- x23 -- c3 -- x31 -- c1.

Each context has a full-support rank-one PVM on the seven satisfying OR3
assignments.  Its selected four-atom Fano cap is q_c.  Every compressed
incidence covariance row A_(c,x) q_c = q_c B_x is exact.  Nevertheless, for
the sequential profile X=q3 q2 q1 and its prescribed spectral source P, the
raw prefix row at (c3,x31) has normalized squared Hilbert--Schmidt norm 1/7.

All calculations use Fraction.  The only rotated atom is represented by its
rational rank-one projection, so no floating-point tolerance is involved.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import factorial


Scalar = Fraction
Matrix = list[list[Scalar]]
Label = tuple[int, int, int]

N = 7
ZERO = Fraction(0)
ONE = Fraction(1)
HALF = Fraction(1, 2)


def zero() -> Matrix:
    return [[ZERO for _ in range(N)] for _ in range(N)]


def identity() -> Matrix:
    result = zero()
    for index in range(N):
        result[index][index] = ONE
    return result


def add(*matrices: Matrix) -> Matrix:
    return [
        [sum((matrix[row][column] for matrix in matrices), ZERO) for column in range(N)]
        for row in range(N)
    ]


def scale(scalar: Scalar, matrix: Matrix) -> Matrix:
    return [[scalar * entry for entry in row] for row in matrix]


def multiply(left: Matrix, right: Matrix) -> Matrix:
    return [
        [
            sum(
                (left[row][middle] * right[middle][column] for middle in range(N)),
                ZERO,
            )
            for column in range(N)
        ]
        for row in range(N)
    ]


def transpose(matrix: Matrix) -> Matrix:
    return [[matrix[column][row] for column in range(N)] for row in range(N)]


def subtract(left: Matrix, right: Matrix) -> Matrix:
    return add(left, scale(-ONE, right))


def diagonal(entries: list[int]) -> Matrix:
    result = zero()
    for index, entry in enumerate(entries):
        result[index][index] = Fraction(entry)
    return result


def coordinate_projection(index: int) -> Matrix:
    result = zero()
    result[index][index] = ONE
    return result


def rotated_projection(left: int, right: int, sign: int) -> Matrix:
    """Projection onto (e_left + sign e_right)/sqrt(2)."""
    result = zero()
    result[left][left] = HALF
    result[right][right] = HALF
    result[left][right] = Fraction(sign, 2)
    result[right][left] = Fraction(sign, 2)
    return result


def trace(matrix: Matrix) -> Scalar:
    return sum((matrix[index][index] for index in range(N)), ZERO)


def hs_squared(matrix: Matrix) -> Scalar:
    return trace(multiply(transpose(matrix), matrix)) / N


def is_zero(matrix: Matrix) -> bool:
    return all(entry == ZERO for row in matrix for entry in row)


def is_signed_permutation(matrix: Matrix) -> bool:
    return all(
        sum(entry != ZERO for entry in row) == 1
        and sum(abs(entry) for entry in row) == ONE
        for row in matrix
    ) and all(
        sum(matrix[row][column] != ZERO for row in range(N)) == 1
        for column in range(N)
    )


def assert_projection(matrix: Matrix) -> None:
    assert transpose(matrix) == matrix
    assert multiply(matrix, matrix) == matrix


OR3: tuple[Label, ...] = tuple(
    label for label in product((0, 1), repeat=3) if label != (0, 0, 0)
)


def cap(normal: Label) -> set[Label]:
    return {
        label
        for label in OR3
        if sum(left * right for left, right in zip(normal, label)) % 2 == 1
    }


E = [coordinate_projection(index) for index in range(N)]
F_PLUS = rotated_projection(0, 4, 1)
F_MINUS = rotated_projection(0, 4, -1)


def context_pvm(assignments: dict[Label, Matrix]) -> dict[Label, Matrix]:
    assert set(assignments) == set(OR3)
    for atom in assignments.values():
        assert_projection(atom)
        assert trace(atom) == ONE
    for left in OR3:
        for right in OR3:
            if left != right:
                assert is_zero(multiply(assignments[left], assignments[right]))
    assert add(*assignments.values()) == identity()
    return assignments


# c1 uses the cap x31=1.  Its cap basis is e0,e1,e2,e3.
C1 = context_pvm(
    {
        (1, 1, 0): E[0],
        (1, 0, 0): E[1],
        (1, 0, 1): E[2],
        (1, 1, 1): E[3],
        (0, 0, 1): E[4],
        (0, 1, 0): E[5],
        (0, 1, 1): E[6],
    }
)

# c2 uses the odd-parity cap.  Its first cap atom is the rotated + line.
C2 = context_pvm(
    {
        (1, 0, 0): F_PLUS,
        (0, 1, 0): E[1],
        (0, 0, 1): E[2],
        (1, 1, 1): E[5],
        (0, 1, 1): F_MINUS,
        (1, 0, 1): E[3],
        (1, 1, 0): E[6],
    }
)

# c3 also uses the odd-parity cap, on e0,e4,e1,e5.
C3 = context_pvm(
    {
        (1, 0, 0): E[0],
        (0, 0, 1): E[4],
        (1, 1, 1): E[1],
        (0, 1, 0): E[5],
        (0, 1, 1): E[2],
        (1, 0, 1): E[3],
        (1, 1, 0): E[6],
    }
)


def observable(pvm: dict[Label, Matrix], coordinate: int) -> Matrix:
    return add(
        *(scale(Fraction((-1) ** label[coordinate]), atom) for label, atom in pvm.items())
    )


def selected_cap(pvm: dict[Label, Matrix], normal: Label) -> Matrix:
    return add(*(pvm[label] for label in cap(normal)))


Q1 = selected_cap(C1, (1, 0, 0))
Q2 = selected_cap(C2, (1, 1, 1))
Q3 = selected_cap(C3, (1, 1, 1))

for projection in (Q1, Q2, Q3):
    assert_projection(projection)
    assert trace(projection) == 4

# The commuting global shared-variable involutions.
B31 = diagonal([-1, -1, -1, -1, 1, 1, 1])
B12 = diagonal([-1, 1, 1, -1, -1, -1, 1])
B23 = diagonal([1, -1, 1, 1, 1, -1, 1])

for involution in (B31, B12, B23):
    assert transpose(involution) == involution
    assert multiply(involution, involution) == identity()

assert is_zero(subtract(multiply(B31, B12), multiply(B12, B31)))
assert is_zero(subtract(multiply(B12, B23), multiply(B23, B12)))
assert is_zero(subtract(multiply(B23, B31), multiply(B31, B23)))

# Every compressed incidence covariance row is exactly zero.
INCIDENCE_ROWS = (
    (observable(C1, 0), Q1, B31, "c1:x31"),
    (observable(C1, 1), Q1, B12, "c1:x12"),
    (observable(C2, 0), Q2, B12, "c2:x12"),
    (observable(C2, 1), Q2, B23, "c2:x23"),
    (observable(C3, 0), Q3, B31, "c3:x31"),
    (observable(C3, 1), Q3, B23, "c3:x23"),
)

for local, carrier, global_observable, _ in INCIDENCE_ROWS:
    row = subtract(multiply(local, carrier), multiply(carrier, global_observable))
    assert is_zero(row)

# Every displayed involution, including each cap reflection and the eventual
# source reflection, lies in the natural signed-permutation group B_7.
for involution in (
    B31,
    B12,
    B23,
    *(local for local, _, _, _ in INCIDENCE_ROWS),
    *(subtract(scale(2, carrier), identity()) for carrier in (Q1, Q2, Q3)),
):
    assert is_signed_permutation(involution)

# Sequential Gram data.  X^*X=diag(1/2,1,0,...,0), so a=3/14 and the
# threshold a/2=3/28 selects P=e0+e1.
X = multiply(Q3, multiply(Q2, Q1))
GRAM = multiply(transpose(X), X)
EXPECTED_GRAM = diagonal([0, 1, 0, 0, 0, 0, 0])
EXPECTED_GRAM[0][0] = HALF
assert GRAM == EXPECTED_GRAM

A = trace(GRAM) / N
assert A == Fraction(3, 14)
P = add(E[0], E[1])
assert_projection(P)
assert is_signed_permutation(subtract(scale(2, P), identity()))

Y3 = multiply(X, P)
RAW_ROW = subtract(multiply(observable(C3, 0), Y3), multiply(Y3, B31))
assert hs_squared(RAW_ROW) == Fraction(1, 7)

# The exact prefix telescope has only the c2 nonincidence commutator left:
# q3 [B31,q2] q1 P.  The c3 local row, [B31,q1], and [B31,P] vanish.
NONINCIDENCE = multiply(
    Q3,
    multiply(
        subtract(multiply(B31, Q2), multiply(Q2, B31)),
        multiply(Q1, P),
    ),
)
assert RAW_ROW == NONINCIDENCE
assert hs_squared(NONINCIDENCE) == Fraction(1, 7)

# In the natural irreducible block of B_7, normalized canonical regular trace
# is (7/|B_7|) times the ordinary matrix trace.
B7_ORDER = (2**N) * factorial(N)
CANONICAL_PROFILE_MASS = Fraction(N, B7_ORDER) * trace(GRAM)
CANONICAL_SOURCE_MASS = Fraction(N, B7_ORDER) * trace(P)
CANONICAL_RAW_HS2 = Fraction(N, B7_ORDER) * trace(
    multiply(transpose(RAW_ROW), RAW_ROW)
)
assert B7_ORDER == 645120
assert CANONICAL_PROFILE_MASS == Fraction(1, 61440)
assert CANONICAL_SOURCE_MASS == Fraction(1, 46080)
assert CANONICAL_RAW_HS2 == Fraction(1, 92160)


def main() -> None:
    print("dimension=7 (minimal for a full-support seven-atom OR3 PVM)")
    print("cap_ranks=4,4,4")
    print("all_six_incidence_rows_hs2=0")
    print(f"sequential_mass_a={A}")
    print("gram_spectrum=1,1/2,0,0,0,0,0")
    print("threshold=a/2=3/28; source_rank=2")
    print(f"raw_prefix_covariance_hs2={hs_squared(RAW_ROW)}")
    print(f"nonincidence_commutator_term_hs2={hs_squared(NONINCIDENCE)}")
    print(f"B7_order={B7_ORDER}")
    print(f"canonical_selected_profile_mass={CANONICAL_PROFILE_MASS}")
    print(f"canonical_selected_source_mass={CANONICAL_SOURCE_MASS}")
    print(f"canonical_selected_raw_hs2={CANONICAL_RAW_HS2}")


if __name__ == "__main__":
    main()
