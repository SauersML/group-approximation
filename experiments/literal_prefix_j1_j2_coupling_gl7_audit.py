"""Audit literal prefix coupling of J1 and J2 in the GL7(F2) chart.

Run through the MSI wrapper only.  The two native Whiteheads become
adjacent transpositions, so their literal factors and braid are exact while
the marked child on the second branch survives.
"""

from experiments.first_native_diamond_cross_return_gl7_c2_audit import (
    ONE,
    commutator,
    multiply,
    transvection,
)


def main():
    # Vertex order: (7_0, 9, 8_0, 7_1, 10, 8_1, 6).
    seven_0, nine, eight_0, seven_1, _ten, eight_1, _six = range(7)

    x1 = transvection(eight_0, seven_0)
    y1 = transvection(seven_0, eight_0)
    x2 = transvection(nine, eight_0)
    y2 = transvection(eight_0, nine)

    left_x = x2
    right_x = y1
    intermediate_x = commutator(left_x, x1)
    assert intermediate_x == transvection(nine, seven_0)
    assert commutator(intermediate_x, right_x) == x2

    right_y = y2
    left_y = x1
    intermediate_y = commutator(y1, right_y)
    assert intermediate_y == transvection(seven_0, nine)
    assert commutator(left_y, intermediate_y) == y2

    j1 = multiply(multiply(x1, y1), x1)
    j2 = multiply(multiply(x2, y2), x2)
    assert multiply(j1, j1) == ONE
    assert multiply(j2, j2) == ONE
    assert multiply(multiply(j1, j2), j1) == multiply(
        multiply(j2, j1), j2
    )

    marked_child = transvection(seven_1, eight_1)
    assert marked_child != ONE
    print("literal J1-J2 prefix coupling closes in GL7(F2); mark survives")


if __name__ == "__main__":
    main()
