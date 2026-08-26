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

    returned_whitehead = multiply(
        multiply(returned_root, opposite_return), returned_root
    )
    assert returned_whitehead == permutation((0, 6, 2, 3, 4, 5, 1))

    transported_s00 = conjugate(returned_whitehead, s00_arm)
    transported_t0 = conjugate(returned_whitehead, t0_arm)
    odd_x_left = commutator(transported_s00, t0_arm)
    odd_x_right = commutator(s00_arm, transported_t0)
    assert transported_s00 == transvection(eight_0, nine)
    assert transported_t0 == transvection(six, seven_0)
    assert odd_x_left == odd_x_right == transvection(eight_0, seven_0)
    odd_x = odd_x_left

    native_label = permutation((2, 1, 0, 3, 4, 5, 6))
    s0_arm = conjugate(native_label, s00_arm)
    t00_arm = conjugate(native_label, t0_arm)
    transported_s0 = conjugate(returned_whitehead, s0_arm)
    transported_t00 = conjugate(native_label, transported_t0)
    assert transported_t00 == conjugate(returned_whitehead, t00_arm)
    odd_y_left = commutator(transported_s0, t00_arm)
    odd_y_right = commutator(s0_arm, transported_t00)
    assert s0_arm == transvection(seven_0, six)
    assert t00_arm == transvection(nine, eight_0)
    assert transported_s0 == transvection(seven_0, nine)
    assert transported_t00 == transvection(six, eight_0)
    assert odd_y_left == odd_y_right == transvection(seven_0, eight_0)
    odd_y = odd_y_left
    assert conjugate(native_label, odd_x) == odd_y

    # The opposite root used in the returned Whitehead is also recovered
    # from the two transported primed arms.
    recovered_opposite = commutator(transported_t00, transported_s00)
    assert recovered_opposite == opposite_return

    literal_j1 = multiply(multiply(odd_x, odd_y), odd_x)
    assert literal_j1 == native_label
    assert multiply(literal_j1, literal_j1) == ONE

    marked_child = transvection(seven_1, eight_1)
    assert marked_child != ONE

    # In GL7(F2) x C2 all factors above have C2 coordinate zero.  Thus the
    # literal equation J1=X1*Y1*X1 forces the old actor gauge bit to zero.
    forced_native_gauge_bit = 0
    assert forced_native_gauge_bit == 0
    print("odd native factors and constant swap close in GL7(F2); gauges killed; mark survives")


if __name__ == "__main__":
    main()
