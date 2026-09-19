"""Exact GL6(F2) model for the depth-two A3 table with private Whiteheads.

Run through the MSI wrapper, never locally.
"""


SIZE = 6
IDENTITY = tuple(1 << index for index in range(SIZE))


def multiply(left, right):
    rows = []
    for left_row in left:
        row = 0
        for index in range(SIZE):
            if (left_row >> index) & 1:
                row ^= right[index]
        rows.append(row)
    return tuple(rows)


def inverse(matrix):
    rows = [matrix[index] | (1 << (SIZE + index)) for index in range(SIZE)]
    for column in range(SIZE):
        pivot = next(index for index in range(column, SIZE) if (rows[index] >> column) & 1)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for index in range(SIZE):
            if index != column and ((rows[index] >> column) & 1):
                rows[index] ^= rows[column]
    return tuple(row >> SIZE for row in rows)


def transvection(row, column):
    matrix = list(IDENTITY)
    matrix[row - 1] ^= 1 << (column - 1)
    return tuple(matrix)


def commutator(left, right):
    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def conjugate(actor, element):
    return multiply(multiply(actor, element), inverse(actor))


def whitehead(forward, reverse):
    return multiply(multiply(forward, reverse), forward)


def main():
    # Marked A3 packet in the first four coordinates.
    A = transvection(1, 2)
    B = transvection(2, 3)
    C = transvection(3, 6)
    D = commutator(A, B)
    E = commutator(B, C)
    P = transvection(1, 6)

    # The cross-zero gamma shortcut occupies its own literal root-role block.
    G = transvection(5, 6)

    assert commutator(D, C) == P
    assert commutator(A, E) == P
    assert commutator(A, G) == IDENTITY
    assert commutator(A, C) == IDENTITY
    assert commutator(B, G) == IDENTITY
    assert commutator(C, G) == IDENTITY
    assert P != IDENTITY

    reverse = {
        "A": transvection(2, 1),
        "B": transvection(3, 2),
        "G": transvection(6, 5),
        "P": transvection(6, 1),
    }
    forward = {"A": A, "B": B, "G": G, "P": P}
    for name in ("A", "B", "G", "P"):
        word = whitehead(forward[name], reverse[name])
        assert multiply(word, word) == IDENTITY
        assert conjugate(word, forward[name]) == reverse[name]
        assert conjugate(word, reverse[name]) == forward[name]

    # The A and B opposite roots also retain the literal zero-incidence rows.
    assert commutator(reverse["A"], B) == IDENTITY
    assert commutator(reverse["A"], C) == IDENTITY
    assert commutator(reverse["A"], G) == IDENTITY
    assert commutator(reverse["B"], A) == IDENTITY
    assert commutator(reverse["B"], C) == IDENTITY
    assert commutator(reverse["B"], G) == IDENTITY

    # The nonzero interaction created by the private G opposite is retained:
    # [C,G^-]=H and [H,G]=C, rather than killing the intermediate arm.
    H = commutator(C, reverse["G"])
    assert H != IDENTITY
    assert commutator(H, G) == C

    print("GL6 depth-two A3 private-arm Whitehead model: exact")
    print("marked transvection nontrivial:", P != IDENTITY)


if __name__ == "__main__":
    main()
