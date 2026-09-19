"""Audit both native order-seven heads in the literal J1/J2 GL7 chart.

Run through the MSI wrapper only.  This is a scoped occurrence model, not a
representation of the full Leavitt elementary group.
"""

from experiments.first_native_diamond_cross_return_gl7_c2_audit import (
    ONE,
    commutator,
    multiply,
    transvection,
)


def power(matrix, exponent):
    result = ONE
    for _ in range(exponent):
        result = multiply(result, matrix)
    return result


def main():
    # Vertex order: (7_0, 9, 8_0, 7_1, 10, 8_1, 6).
    seven_0, nine, eight_0, seven_1, ten, eight_1, six = range(7)

    x1 = transvection(eight_0, seven_0)
    y1 = transvection(seven_0, eight_0)
    x2 = transvection(nine, eight_0)
    y2 = transvection(eight_0, nine)
    # Use two adjacent GL3 triangles.  This retains distinct occurrences for
    # all four literal center-chain arms instead of identifying an arm with a
    # prefix factor in the scoped model.
    a1 = transvection(six, seven_0)
    b2 = transvection(eight_0, six)
    a2 = transvection(ten, eight_0)
    b3 = transvection(nine, ten)
    assert commutator(b2, a1) == x1
    assert commutator(b3, a2) == x2
    assert commutator(b3, a1) == ONE

    j1 = multiply(multiply(x1, y1), x1)
    j2 = multiply(multiply(x2, y2), x2)
    v1 = multiply(b2, a1)
    v2 = multiply(b3, a2)

    assert power(multiply(j1, v1), 7) == ONE
    assert power(multiply(j2, v2), 7) == ONE
    assert multiply(multiply(j1, j2), j1) == multiply(
        multiply(j2, j1), j2
    )

    marked_child = transvection(seven_1, eight_1)
    assert marked_child != ONE
    print("both prefix order-seven heads close in GL7(F2); mark survives")


if __name__ == "__main__":
    main()
