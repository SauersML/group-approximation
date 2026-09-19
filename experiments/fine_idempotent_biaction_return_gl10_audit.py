"""Audit the literal fine-idempotent biaction return in GL10(F2).

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
    # Old chart: (7_0, 9, 8_0, 7_1, 10, 8_1, 6, u); then add (v,h).
    seven_0, nine, eight_0, seven_1, ten, eight_1, six, u, v, h = range(10)

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

    # Retain the marked-center return and its first constant Whitehead.
    a3 = transvection(u, nine)
    c3 = commutator(a3, b3)
    returned_a2 = commutator(c3, a2)
    p = swap(u, ten)
    assert c3 == transvection(u, ten)
    assert returned_a2 == transvection(u, eight_0)
    assert conjugate(p, a2) == returned_a2

    # Retain the native A2 factorization and its parallel return path.
    s1 = transvection(ten, seven_0)
    t00 = transvection(seven_0, eight_0)
    assert commutator(s1, t00) == a2
    assert commutator(conjugate(p, s1), t00) == returned_a2

    q = swap(seven_0, nine)
    assert conjugate(q, conjugate(p, s1)) == transvection(u, nine)
    assert conjugate(q, t00) == transvection(nine, eight_0)
    assert conjugate(q, returned_a2) == returned_a2

    # Factor B2 through the actual s_00,t_1 occurrences.
    s00 = transvection(eight_0, h)
    t1 = transvection(h, six)
    assert commutator(s00, t1) == b2

    # K=(8 v)(6 10) transports the whole B2 factorization.
    k = multiply(swap(eight_0, v), swap(six, ten))
    bar_s00 = conjugate(k, s00)
    bar_t1 = conjugate(k, t1)
    bar_b2 = conjugate(k, b2)
    assert bar_s00 == transvection(v, h)
    assert bar_t1 == transvection(h, ten)
    assert bar_b2 == transvection(v, ten)
    assert commutator(bar_s00, bar_t1) == bar_b2

    # The reverse product is the literal fine idempotent e_00.
    fine_idempotent = commutator(bar_b2, a2)
    assert fine_idempotent == transvection(v, eight_0)

    # One constant Whitehead exposes both absorption identities
    # e_00 s_00=s_00 and t_00 e_00=t_00 on the same occurrences.
    ell = swap(v, eight_0)
    moved_s00 = conjugate(ell, bar_s00)
    moved_t00 = conjugate(ell, t00)
    assert moved_s00 == transvection(eight_0, h)
    assert moved_t00 == transvection(seven_0, v)
    assert commutator(fine_idempotent, moved_s00) == bar_s00
    assert commutator(moved_t00, fine_idempotent) == t00

    # Factor every named constant swap by three elementary transvections.
    for left, right, permutation in (
        (u, ten, p),
        (seven_0, nine, q),
        (v, eight_0, ell),
    ):
        x = transvection(left, right)
        y = transvection(right, left)
        assert multiply(multiply(x, y), x) == permutation

    marked_child = transvection(seven_1, eight_1)
    assert marked_child != ONE
    print("fine-idempotent two-sided return closes in GL10(F2); mark survives")


if __name__ == "__main__":
    main()
