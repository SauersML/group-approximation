"""Audit the native A1--B2 Hecke triangle in the GL7(F2) chart.

Run through the MSI wrapper only.  The literal A1 and B2 occurrences are
compiled through the already named t0 and returned s00 arms.  Their Hecke
head has order seven, while the marked child on the other branch survives.
"""

from experiments.first_native_diamond_cross_return_gl7_c2_audit import (
    ONE,
    commutator,
    multiply,
    permutation,
    transvection,
)


def power(element, exponent):
    answer = ONE
    for _ in range(exponent):
        answer = multiply(answer, element)
    return answer


def main():
    # Vertex order: (7_0, 9, 8_0, 7_1, 10, 8_1, 6).
    seven_0, nine, eight_0, seven_1, _ten, eight_1, six = range(7)

    # The authenticated first native actor and its literal prefix successor.
    x1 = transvection(eight_0, seven_0)
    y1 = transvection(seven_0, eight_0)
    x2 = transvection(nine, eight_0)
    y2 = transvection(eight_0, nine)
    j1 = multiply(multiply(x1, y1), x1)
    j2 = multiply(multiply(x2, y2), x2)
    assert j1 == permutation((2, 1, 0, 3, 4, 5, 6))
    assert multiply(multiply(j1, j2), j1) == multiply(
        multiply(j2, j1), j2
    )

    # Existing literal occurrences: T0=x_97(t0) and the returned
    # S00=x_89(s00).  Add S1=x_49(s1) and T1=x_94(t1).  The two ordinary
    # path commutators are precisely A1=x_47(s1*t0) and
    # B2=x_84(s00*t1).
    t0 = transvection(nine, seven_0)
    s00 = transvection(eight_0, nine)
    s1 = transvection(six, nine)
    t1 = transvection(nine, six)
    a1 = commutator(s1, t0)
    b2 = commutator(s00, t1)
    assert a1 == transvection(six, seven_0)
    assert b2 == transvection(eight_0, six)

    # This is the literal center-chain product root X1=x_87(s00*t0).
    assert commutator(b2, a1) == x1

    # On (6,7_0,8_0), (A1,B2,J1) is the natural GL3(F2) packet.
    hecke_head = multiply(multiply(j1, b2), a1)
    assert power(hecke_head, 7) == ONE
    assert all(power(hecke_head, exponent) != ONE for exponent in range(1, 7))

    marked_child = transvection(seven_1, eight_1)
    assert marked_child != ONE
    print("native A1-B2 Hecke triangle closes in GL7(F2); mark survives")


if __name__ == "__main__":
    main()
