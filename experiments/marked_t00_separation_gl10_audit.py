"""Audit the paid t00/Y1 separation and its transverse GL10(F2) model.

Run through the MSI wrapper only.
"""


DIMENSION = 10


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


def swap_product(*pairs):
    mapping = list(range(DIMENSION))
    for first, second in pairs:
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
    # Vertex order: (7_0,9,8_0,7_1,10,8_1,6,u,b,c).
    seven_0, nine, eight_0, seven_1, ten, eight_1, six, u, b, c = range(10)

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
    assert commutator(b2, a1) == x1
    assert commutator(b3, a2) == x2
    assert power(multiply(multiply(j1, b2), a1), 7) == ONE
    assert power(multiply(multiply(j2, b3), a2), 7) == ONE

    a3 = transvection(u, nine)
    c3 = commutator(a3, b3)
    returned_a2 = commutator(c3, a2)
    assert c3 == transvection(u, ten)
    assert returned_a2 == transvection(u, eight_0)
    p = swap_product((u, ten))
    assert conjugate(p, a2) == returned_a2

    # The paid same-root occurrences are now genuinely different.
    y = y1
    t = transvection(b, eight_0)
    discrepancy = multiply(t, y)
    assert t != y
    assert discrepancy != ONE
    assert commutator(t, y) == ONE

    # Literal t0*(s0*t00)=t00 multiplication row.
    left_t0 = transvection(b, seven_0)
    assert commutator(left_t0, y) == t

    # Native A2 and both returned paths use T.
    s57 = transvection(ten, b)
    assert commutator(s57, t) == a2
    s67 = conjugate(p, s57)
    assert s67 == transvection(u, b)
    assert commutator(s67, t) == returned_a2

    q79 = swap_product((seven_0, nine), (b, c))
    t98 = conjugate(q79, t)
    s69 = conjugate(q79, s67)
    assert conjugate(q79, y) == x2
    assert t98 == transvection(c, eight_0)
    assert s69 == transvection(u, c)
    assert commutator(s69, t98) == returned_a2
    assert conjugate(q79, returned_a2) == returned_a2

    # Exact marked saturation q*d*s00=q.
    q67 = transvection(seven_1, b)
    s00_8k = transvection(eight_0, eight_1)
    qd = commutator(q67, discrepancy)
    marked_child = commutator(qd, s00_8k)
    assert qd == transvection(seven_1, eight_0)
    assert marked_child == transvection(seven_1, eight_1)
    assert marked_child != ONE

    print("paid t00/Y1 separation remains transverse in GL10(F2)")


if __name__ == "__main__":
    main()
