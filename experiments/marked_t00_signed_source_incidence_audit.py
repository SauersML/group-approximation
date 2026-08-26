"""Audit signed-Hecke incidence of the paid t00 discrepancy in GL12(F2).

Run through the MSI wrapper only.  The model extends the exact transverse
GL10 occurrence chart by the literal UT4 center chain and the two row-two
source roots.  Traces are evaluated exactly in the permutation representation
on F2^12 using fixed-space dimensions; no dense matrices are allocated.
"""

from collections import deque
from fractions import Fraction


DIMENSION = 12


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


def matrix_rank(matrix):
    rows = []
    for i in range(DIMENSION):
        row = 0
        for j, column in enumerate(matrix):
            if (column >> i) & 1:
                row |= 1 << j
        rows.append(row)
    rank = 0
    for column in range(DIMENSION):
        pivot = next((r for r in range(rank, DIMENSION) if (rows[r] >> column) & 1), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for r in range(DIMENSION):
            if r != rank and ((rows[r] >> column) & 1):
                rows[r] ^= rows[rank]
        rank += 1
    return rank


def fixed_points(matrix):
    difference = tuple(matrix[i] ^ ONE[i] for i in range(DIMENSION))
    return 1 << (DIMENSION - matrix_rank(difference))


def generated_with_character(generators):
    """Enumerate a finite group and the character negative on each generator."""
    character = {ONE: 1}
    queue = deque([ONE])
    while queue:
        current = queue.popleft()
        for generator in generators:
            nxt = multiply(current, generator)
            sign = -character[current]
            if nxt in character:
                assert character[nxt] == sign
            else:
                character[nxt] = sign
                queue.append(nxt)
    return character


def main():
    # Old vertices followed by the two new center-chain vertices r,s.
    seven_0, nine, eight_0, seven_1, ten, eight_1, six, u, b, c, r, s = range(12)

    x1 = transvection(eight_0, seven_0)
    y1 = transvection(seven_0, eight_0)
    x2 = transvection(nine, eight_0)
    y2 = transvection(eight_0, nine)
    j1 = multiply(multiply(x1, y1), x1)
    j2 = multiply(multiply(x2, y2), x2)
    assert multiply(multiply(j1, j2), j1) == multiply(multiply(j2, j1), j2)

    a1 = transvection(six, seven_0)
    b2 = transvection(eight_0, six)
    a2 = transvection(ten, eight_0)
    b3 = transvection(nine, ten)
    assert commutator(b2, a1) == x1
    assert commutator(b3, a2) == x2
    assert power(multiply(multiply(j1, b2), a1), 7) == ONE
    assert power(multiply(multiply(j2, b3), a2), 7) == ONE

    a3 = transvection(u, nine)
    h3 = commutator(a3, b3)
    returned_a2 = commutator(h3, a2)
    assert h3 == transvection(u, ten)
    assert returned_a2 == transvection(u, eight_0)

    # Paid same-root discrepancy and its marked saturation.
    y = y1
    t = transvection(b, eight_0)
    discrepancy = multiply(t, y)
    assert t != y and discrepancy != ONE and power(discrepancy, 2) == ONE
    left_t0 = transvection(b, seven_0)
    assert commutator(left_t0, y) == t
    s57 = transvection(ten, b)
    assert commutator(s57, t) == a2
    p = swap_product((u, ten))
    s67 = conjugate(p, s57)
    assert commutator(s67, t) == returned_a2
    q79 = swap_product((seven_0, nine), (b, c))
    assert commutator(conjugate(q79, s67), conjugate(q79, t)) == returned_a2

    q67 = transvection(seven_1, b)
    s00_8k = transvection(eight_0, eight_1)
    mark = commutator(commutator(q67, discrepancy), s00_8k)
    assert mark == transvection(seven_1, eight_1)

    # Literal center chain H=<x65(q),x54(q),x42(q)> and row-two source U.
    h2 = transvection(ten, r)
    h1 = transvection(r, s)
    source_f = commutator(b3, h2)
    derived_h21 = commutator(h2, h1)
    source_k = commutator(b3, derived_h21)
    assert source_f == transvection(nine, r)
    assert source_k == transvection(nine, s)
    assert commutator(source_f, source_k) == ONE

    hecke_character = generated_with_character((h3, h2, h1))
    assert len(hecke_character) == 64
    source_group = (ONE, source_f, source_k, multiply(source_f, source_k))

    # Every projector factor commutes, so trace products reduce to signed
    # fixed-point sums in the 4096-point permutation representation.
    assert commutator(mark, discrepancy) == ONE
    for element in tuple(hecke_character) + source_group:
        assert commutator(mark, element) == ONE
        assert commutator(discrepancy, element) == ONE

    base_dimension = 1 << DIMENSION

    def normalized_trace_sum(include_mark, include_discrepancy, tensor_power):
        total = 0
        for mark_power in range(2 if include_mark else 1):
            mark_coefficient = -1 if mark_power else 1
            mark_element = mark if mark_power else ONE
            for d_power in range(2 if include_discrepancy else 1):
                d_coefficient = -1 if d_power else 1
                d_element = discrepancy if d_power else ONE
                for h, h_sign in hecke_character.items():
                    for source_element in source_group:
                        word = multiply(
                            multiply(mark_element, d_element),
                            multiply(h, source_element),
                        )
                        total += (
                            mark_coefficient
                            * d_coefficient
                            * h_sign
                            * fixed_points(word) ** tensor_power
                        )
        denominator = (
            len(hecke_character)
            * len(source_group)
            * base_dimension ** tensor_power
        )
        if include_mark:
            denominator *= 2
        if include_discrepancy:
            denominator *= 2
        return Fraction(total, denominator)

    for tensor_power in range(1, 9):
        source_trace = normalized_trace_sum(False, False, tensor_power)
        marked_source_trace = normalized_trace_sum(True, False, tensor_power)
        paid_source_trace = normalized_trace_sum(True, True, tensor_power)
        assert source_trace >= 0 and marked_source_trace >= 0 and paid_source_trace >= 0
        print(f"tensor power {tensor_power}: source trace={source_trace}")
        print(f"tensor power {tensor_power}: marked source trace={marked_source_trace}")
        print(f"tensor power {tensor_power}: paid marked source trace={paid_source_trace}")


if __name__ == "__main__":
    main()
