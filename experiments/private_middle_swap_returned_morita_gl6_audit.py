"""Audit the private-middle cross return in GL_6(F_2).

Run through the MSI wrapper only.  This script deliberately verifies only
the fixed occurrence table; it does not enumerate GL_6(F_2).
"""


SIZE = 6


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
    for _ in range(1, 128):
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
    # Vertex order: (7_0, 9, 8_0, 7_1, 10, 8_1).
    seven_0, middle_0, eight_0, seven_1, middle_1, eight_1 = range(SIZE)

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

    middle_swap = permutation((0, 4, 2, 3, 1, 5))
    assert multiply(middle_swap, middle_swap) == ONE
    assert commutator(middle_swap, positive_parent) == ONE
    assert commutator(middle_swap, reverse_parent) == ONE

    positive_p = commutator(conjugate(middle_swap, s_0), t_1)
    positive_r = commutator(conjugate(middle_swap, s_1), t_0)
    reverse_p = commutator(conjugate(middle_swap, u_0), v_1)
    reverse_r = commutator(conjugate(middle_swap, u_1), v_0)

    assert positive_p == transvection(seven_0, eight_1)
    assert positive_r == transvection(seven_1, eight_0)
    assert reverse_p == transvection(eight_0, seven_1)
    assert reverse_r == transvection(eight_1, seven_0)

    k_0 = whitehead(positive_p, reverse_r)
    k_1 = whitehead(positive_r, reverse_p)
    branch_flip = multiply(k_0, k_1)
    assert multiply(k_0, k_0) == ONE
    assert multiply(k_1, k_1) == ONE
    assert commutator(k_0, k_1) == ONE
    assert conjugate(branch_flip, positive_parent) == reverse_parent
    assert conjugate(branch_flip, reverse_parent) == positive_parent
    assert commutator(middle_swap, k_0) == ONE
    assert commutator(middle_swap, k_1) == ONE

    for s_i, t_i, c_i, u_i, v_i, r_i in (branch_0, branch_1):
        assert commutator(s_i, t_i) == c_i
        assert commutator(reverse_parent, s_i) == u_i
        assert commutator(t_i, reverse_parent) == v_i
        assert commutator(u_i, v_i) == r_i

    assert multiply(c_0, c_1) == positive_parent
    assert multiply(r_0, r_1) == reverse_parent
    assert multiply(multiply(positive_parent, reverse_parent),
                    positive_parent) == multiply(
                        multiply(reverse_parent, positive_parent),
                        reverse_parent)
    assert c_1 != ONE
    print("fixed GL6(F2) cross-return table verified; marked child survives")


if __name__ == "__main__":
    main()
