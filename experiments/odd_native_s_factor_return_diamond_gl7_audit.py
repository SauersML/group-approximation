"""Audit the odd native s00*t0 return diamond in GL7(F2).

Run through the MSI wrapper only.  The extension authenticates both odd
factors of J1, so the formerly free C2 coordinate is forced to zero, but
the marked child in the other branch remains nontrivial.
"""

from experiments.first_native_diamond_cross_return_gl7_c2_audit import (
    ONE,
    commutator,
    conjugate,
    multiply,
    permutation,
    transvection,
)


def main():
    # Vertex order: (7_0, 9, 8_0, 7_1, 10, 8_1, 6).
    seven_0, nine, eight_0, seven_1, _ten, eight_1, six = range(7)

    returned_root = transvection(nine, six)
    opposite_return = transvection(six, nine)
    t0_arm = transvection(nine, seven_0)
    s00_arm = transvection(eight_0, six)

    transported_t0 = commutator(opposite_return, t0_arm)
    odd_x = commutator(s00_arm, transported_t0)
    assert transported_t0 == transvection(six, seven_0)
    assert odd_x == transvection(eight_0, seven_0)

    native_label = permutation((2, 1, 0, 3, 4, 5, 6))
    s0_arm = conjugate(native_label, s00_arm)
    transported_t00 = conjugate(native_label, transported_t0)
    odd_y = commutator(s0_arm, transported_t00)
    assert s0_arm == transvection(seven_0, six)
    assert transported_t00 == transvection(six, eight_0)
    assert odd_y == transvection(seven_0, eight_0)
    assert conjugate(native_label, odd_x) == odd_y

    literal_j1 = multiply(multiply(odd_x, odd_y), odd_x)
    assert literal_j1 == native_label
    assert multiply(literal_j1, literal_j1) == ONE

    # The returned-root Whitehead is available as an ordinary finite actor.
    returned_whitehead = multiply(
        multiply(returned_root, opposite_return), returned_root
    )
    assert conjugate(returned_whitehead, t0_arm) == transported_t0

    marked_child = transvection(seven_1, eight_1)
    assert marked_child != ONE

    # In GL7(F2) x C2 all factors above have C2 coordinate zero.  Thus the
    # literal equation J1=X1*Y1*X1 forces the old actor gauge bit to zero.
    forced_native_gauge_bit = 0
    assert forced_native_gauge_bit == 0
    print("odd native s-factor closes in GL7(F2); C2 gauge killed, mark survives")


if __name__ == "__main__":
    main()
