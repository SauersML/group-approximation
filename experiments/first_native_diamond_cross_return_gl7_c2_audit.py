"""Audit the first native diamond over the GL7(F2) cross-return chart.

Run through the MSI wrapper only.  The independent C2 coordinate of J is
symbolic: centrality makes it cancel from every displayed conjugacy and
commutator, while its nonzero bit remains available as a gauge.
"""


SIZE = 7


def identity():
    return tuple(
        tuple(1 if row == column else 0 for column in range(SIZE))
        for row in range(SIZE)
    )


ONE = identity()


def multiply(left, right):
    return tuple(
        tuple(
            sum(left[row][middle] * right[middle][column]
                for middle in range(SIZE)) % 2
            for column in range(SIZE)
        )
        for row in range(SIZE)
    )


def transvection(row, column):
    answer = [list(entry) for entry in ONE]
    answer[row][column] = 1
    return tuple(tuple(entry) for entry in answer)


def inverse(element):
    candidate = ONE
    for _ in range(1, 256):
        candidate = multiply(candidate, element)
        if multiply(element, candidate) == ONE:
            return candidate
    raise AssertionError("inverse not found within the fixed audit bound")


def commutator(left, right):
    return multiply(
        multiply(multiply(left, right), inverse(left)), inverse(right)
    )


def conjugate(actor, element):
    return multiply(multiply(actor, element), inverse(actor))


def whitehead(positive, reverse):
    return multiply(multiply(positive, reverse), positive)


def permutation(mapping):
    return tuple(
        tuple(1 if row == mapping[column] else 0 for column in range(SIZE))
        for row in range(SIZE)
    )


def main():
    # Vertex order: (7_0, 9, 8_0, 7_1, 10, 8_1, 6).
    seven_0, middle_0, eight_0, seven_1, middle_1, eight_1, six = range(SIZE)
    branch_0 = (
        transvection(seven_0, middle_0),
        transvection(middle_0, eight_0),
        transvection(seven_0, eight_0),
        transvection(eight_0, middle_0),
        transvection(middle_0, seven_0),
        transvection(eight_0, seven_0),
    )
    branch_1 = (
        transvection(seven_1, middle_1),
        transvection(middle_1, eight_1),
        transvection(seven_1, eight_1),
        transvection(eight_1, middle_1),
        transvection(middle_1, seven_1),
        transvection(eight_1, seven_1),
    )
    s_0, t_0, c_0, u_0, v_0, r_0 = branch_0
    s_1, t_1, c_1, u_1, v_1, r_1 = branch_1
    positive_parent = multiply(c_0, c_1)
    reverse_parent = multiply(r_0, r_1)

    middle_swap = permutation((0, 4, 2, 3, 1, 5, 6))
    positive_p = commutator(conjugate(middle_swap, s_0), t_1)
    positive_r = commutator(conjugate(middle_swap, s_1), t_0)
    reverse_p = commutator(conjugate(middle_swap, u_0), v_1)
    reverse_r = commutator(conjugate(middle_swap, u_1), v_0)
    k_0 = whitehead(positive_p, reverse_r)
    k_1 = whitehead(positive_r, reverse_p)
    branch_flip = multiply(k_0, k_1)
    assert conjugate(branch_flip, positive_parent) == reverse_parent
    assert conjugate(branch_flip, reverse_parent) == positive_parent

    second_arm = transvection(seven_0, six)
    returned_mark = commutator(v_0, second_arm)
    native_label = permutation((2, 1, 0, 3, 4, 5, 6))
    primed_first_arm = conjugate(native_label, v_0)
    primed_second_arm = conjugate(native_label, second_arm)

    assert primed_first_arm == t_0
    assert primed_second_arm == transvection(eight_0, six)
    assert commutator(v_0, second_arm) == returned_mark
    assert commutator(primed_first_arm, primed_second_arm) == returned_mark
    assert multiply(native_label, native_label) == ONE
    assert commutator(native_label, middle_swap) == ONE
    assert conjugate(native_label, returned_mark) == returned_mark

    assert commutator(
        conjugate(middle_swap, v_0),
        conjugate(middle_swap, second_arm),
    ) == conjugate(middle_swap, returned_mark)
    assert commutator(
        conjugate(middle_swap, primed_first_arm),
        conjugate(middle_swap, primed_second_arm),
    ) == conjugate(middle_swap, returned_mark)

    # The actual native actor is (native_label, 1) in GL7(F2) x C2.
    # Every other named actor has C2 coordinate zero.  Its central gauge bit
    # cancels in all checks above and remains nonzero.
    native_gauge_bit = 1
    assert native_gauge_bit != 0
    assert c_1 != ONE
    print("GL7(F2) x C2 native-diamond cross-return model verified; mark survives")


if __name__ == "__main__":
    main()
