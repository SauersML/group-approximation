"""Audit the parallel literal A2/return paths in the marked GL8(F2) chart.

Run through the MSI wrapper only.
"""

from experiments.row2_marked_center_action_return_gl8_audit import (
    ONE,
    commutator,
    conjugate,
    multiply,
    power,
    swap,
    transvection,
)


def main():
    # Vertex order: (7_0, 9, 8_0, 7_1, 10, 8_1, 6, u).
    seven_0, nine, eight_0, seven_1, ten, eight_1, six, u = range(8)

    x1 = transvection(eight_0, seven_0)
    y1 = transvection(seven_0, eight_0)
    x2 = transvection(nine, eight_0)
    y2 = transvection(eight_0, nine)
    j1 = multiply(multiply(x1, y1), x1)
    j2 = multiply(multiply(x2, y2), x2)
    assert multiply(multiply(j1, j2), j1) == multiply(
        multiply(j2, j1), j2
    )

    a1 = transvection(six, seven_0)
    b2 = transvection(eight_0, six)
    a2 = transvection(ten, eight_0)
    b3 = transvection(nine, ten)
    assert power(multiply(multiply(j1, b2), a1), 7) == ONE
    assert power(multiply(multiply(j2, b3), a2), 7) == ONE

    a3 = transvection(u, nine)
    c3 = commutator(a3, b3)
    returned_a2 = commutator(c3, a2)
    assert c3 == transvection(u, ten)
    assert returned_a2 == transvection(u, eight_0)

    root_65 = transvection(u, ten)
    root_56 = transvection(ten, u)
    p = multiply(multiply(root_65, root_56), root_65)
    assert p == swap(u, ten)
    assert conjugate(p, a2) == returned_a2

    # Independently factor the native A2 occurrence.
    s57 = transvection(ten, seven_0)
    t78 = transvection(seven_0, eight_0)
    assert commutator(s57, t78) == a2

    # Transport that whole path through P.
    s67 = conjugate(p, s57)
    assert s67 == transvection(u, seven_0)
    assert conjugate(p, t78) == t78
    assert commutator(s67, t78) == returned_a2

    # The second path uses distinct root occurrences of the same coefficients.
    s69 = transvection(u, nine)
    t98 = transvection(nine, eight_0)
    assert commutator(s69, t98) == returned_a2

    # Factor Q=w_79(1) and compare both factors occurrence by occurrence.
    root_79 = transvection(seven_0, nine)
    root_97 = transvection(nine, seven_0)
    q = multiply(multiply(root_79, root_97), root_79)
    assert q == swap(seven_0, nine)
    assert conjugate(q, s67) == s69
    assert conjugate(q, t78) == t98
    assert conjugate(q, returned_a2) == returned_a2

    marked_child = transvection(seven_1, eight_1)
    assert marked_child != ONE
    print("parallel row-two A2 return diamond closes in GL8(F2); mark survives")


if __name__ == "__main__":
    main()
