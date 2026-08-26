"""Audit the row-two marked-center action return in GL8(F2).

Run through the MSI wrapper only.  This is a scoped occurrence model, not a
representation of the full Leavitt elementary or Steinberg group.
"""


DIMENSION = 8


def identity():
    return tuple(1 << i for i in range(DIMENSION))


ONE = identity()


def multiply(left, right):
    columns = []
    for column in right:
        image = 0
        for bit in range(DIMENSION):
            if (column >> bit) & 1:
                image ^= left[bit]
        columns.append(image)
    return tuple(columns)


def inverse(matrix):
    rows = []
    for i in range(DIMENSION):
        row = 0
        for j, column in enumerate(matrix):
            if (column >> i) & 1:
                row |= 1 << j
        rows.append(row | (1 << (DIMENSION + i)))
    for pivot in range(DIMENSION):
        choice = next(i for i in range(pivot, DIMENSION) if (rows[i] >> pivot) & 1)
        rows[pivot], rows[choice] = rows[choice], rows[pivot]
        for i in range(DIMENSION):
            if i != pivot and ((rows[i] >> pivot) & 1):
                rows[i] ^= rows[pivot]
    answer_rows = [row >> DIMENSION for row in rows]
    columns = []
    for j in range(DIMENSION):
        column = 0
        for i, row in enumerate(answer_rows):
            if (row >> j) & 1:
                column |= 1 << i
        columns.append(column)
    return tuple(columns)


def commutator(left, right):
    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def transvection(target, source):
    columns = list(ONE)
    columns[source] ^= 1 << target
    return tuple(columns)


def permutation(mapping):
    return tuple(1 << mapping[i] for i in range(DIMENSION))


def swap(first, second):
    mapping = list(range(DIMENSION))
    mapping[first], mapping[second] = mapping[second], mapping[first]
    return permutation(mapping)


def conjugate(actor, element):
    return multiply(multiply(actor, element), inverse(actor))


def power(element, exponent):
    answer = ONE
    for _ in range(exponent):
        answer = multiply(answer, element)
    return answer


def main():
    # Vertex order: (7_0, 9, 8_0, 7_1, 10, 8_1, 6, u).
    seven_0, nine, eight_0, seven_1, ten, eight_1, six, u = range(DIMENSION)

    x1 = transvection(eight_0, seven_0)
    y1 = transvection(seven_0, eight_0)
    x2 = transvection(nine, eight_0)
    y2 = transvection(eight_0, nine)
    j1 = multiply(multiply(x1, y1), x1)
    j2 = multiply(multiply(x2, y2), x2)
    assert j1 == swap(seven_0, eight_0)
    assert j2 == swap(eight_0, nine)
    assert multiply(multiply(j1, j2), j1) == multiply(
        multiply(j2, j1), j2
    )

    a1 = transvection(six, seven_0)
    b2 = transvection(eight_0, six)
    a2 = transvection(ten, eight_0)
    b3 = transvection(nine, ten)
    assert commutator(b2, a1) == x1
    assert commutator(b3, a2) == x2
    assert power(multiply(multiply(j1, b2), a1), 7) == ONE
    assert power(multiply(multiply(j2, b3), a2), 7) == ONE

    # A3 and B3 form the marked q-center C3.  C3 acts as the identity on
    # the coefficient of the literal A2 arm.
    a3 = transvection(u, nine)
    c3 = commutator(a3, b3)
    assert c3 == transvection(u, ten)
    returned_a2 = commutator(c3, a2)
    assert returned_a2 == transvection(u, eight_0)

    # Factor the literal constant Whitehead w_65(1), not merely an anonymous
    # permutation, and compare its transport of the same A2 occurrence.
    root_65_one = transvection(u, ten)
    root_56_one = transvection(ten, u)
    p = multiply(multiply(root_65_one, root_56_one), root_65_one)
    assert p == swap(u, ten)
    assert conjugate(p, a2) == returned_a2

    # The constant swap is disjoint from the complete first-row triangle
    # and from both prefix actors.
    for element in (a1, b2, j1, j2):
        assert commutator(p, element) == ONE

    marked_child = transvection(seven_1, eight_1)
    k = multiply(swap(seven_1, u), swap(eight_1, ten))
    assert conjugate(k, marked_child) == c3
    assert marked_child != ONE

    print("row-two marked-center action return closes in GL8(F2); mark survives")


if __name__ == "__main__":
    main()
