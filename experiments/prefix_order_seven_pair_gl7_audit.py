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
    seven_0, nine, eight_0, seven_1, _ten, eight_1, _six = range(7)

    x1 = transvection(eight_0, seven_0)
    y1 = transvection(seven_0, eight_0)
    x2 = transvection(nine, eight_0)
    y2 = transvection(eight_0, nine)
    u = transvection(nine, seven_0)

    # The two literal Hecke heads fold into the same triangle:
    # B2=Y2, A1=U and B3=U, A2=Y1.  Their commutators are precisely
    # the two native first factors X1 and X2.
    b2, a1 = y2, u
    b3, a2 = u, y1
    assert commutator(b2, a1) == x1
    assert commutator(b3, a2) == x2

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
