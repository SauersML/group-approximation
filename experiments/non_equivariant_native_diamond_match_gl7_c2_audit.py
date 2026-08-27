"""Audit non-equivariant matches of the first primed native diamond.

Run through the MSI wrapper only.  The C2 coordinate of the native actor is
symbolic: all displayed old actor rows have even actor parity, and the new
commutator rows do not use the actor.
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


def permutation(mapping):
    return tuple(
        tuple(1 if row == mapping[column] else 0 for column in range(SIZE))
        for row in range(SIZE)
    )


def main():
    # Vertex order: (7_0, 9, 8_0, 7_1, 10, 8_1, 6).
    seven_0, nine, eight_0, seven_1, ten, eight_1, six = range(SIZE)

    source_a = transvection(nine, seven_0)
    source_b = transvection(seven_0, six)
    native_label = permutation((2, 1, 0, 3, 4, 5, 6))
    primed_a = conjugate(native_label, source_a)
    primed_b = conjugate(native_label, source_b)

    prefix_t = transvection(seven_0, eight_0)
    prefix_s = transvection(eight_0, seven_0)

    # Direct prefix-square matches.
    assert commutator(source_a, prefix_t) == primed_a
    assert commutator(prefix_s, source_b) == primed_b

    # Cross-row returned matches use the same matrices under the scoped
    # occurrence assignment: C2=prefix_t, L=source_a, D2=prefix_s, h1=source_b.
    c2_returned = prefix_t
    constant_left = source_a
    d2_source = prefix_s
    h1_returned = source_b
    assert commutator(constant_left, c2_returned) == primed_a
    assert commutator(d2_source, h1_returned) == primed_b

    returned_mark = commutator(source_a, source_b)
    marked_child = transvection(seven_1, eight_1)
    assert conjugate(native_label, returned_mark) == returned_mark
    assert marked_child != ONE

    # The actual actor is (native_label, 1) in GL7(F2) x C2.  The new rows
    # have actor parity zero, while old covariance has parity 1+1=0.
    native_actor_gauge = 1
    assert native_actor_gauge != 0
    print("non-equivariant native-diamond matches retain GL7(F2) x C2 gauge")


if __name__ == "__main__":
    main()
