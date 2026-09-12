"""Verify the balanced-cross rectangular Morita escape.

Run on MSI only.  The displayed Leavitt coefficients are represented by
matrix units in M_3(F_2): the two range objects use coordinates 0 and 1,
while the still-unidentified common source uses coordinate 2.  Elementary
root matrices over M_3(F_2) are flattened to matrices over F_2.
"""


def identity(size):
    return tuple(
        tuple(1 if row == column else 0 for column in range(size))
        for row in range(size)
    )


def add(left, right):
    return tuple(
        tuple(a ^ b for a, b in zip(left_row, right_row))
        for left_row, right_row in zip(left, right)
    )


def multiply(left, right):
    size = len(left)
    return tuple(
        tuple(
            sum(left[row][middle] * right[middle][column]
                for middle in range(size)) % 2
            for column in range(size)
        )
        for row in range(size)
    )


def matrix_unit(row, column):
    answer = [[0] * 3 for _ in range(3)]
    answer[row][column] = 1
    return tuple(tuple(entry) for entry in answer)


def root(row, column, coefficient, root_size=7):
    """I + E_(row,column) tensor coefficient over F_2."""
    block_size = 3
    size = root_size * block_size
    answer = [list(entry) for entry in identity(size)]
    for i in range(block_size):
        for j in range(block_size):
            answer[row * block_size + i][column * block_size + j] ^= coefficient[i][j]
    return tuple(tuple(entry) for entry in answer)


def commutator(left, right):
    # Every root transvection used as an input below is an involution.  The
    # products passed here are also inverted by a short power search.
    def inverse(element):
        candidate = identity(len(element))
        for _ in range(1, 64):
            candidate = multiply(candidate, element)
            if multiply(element, candidate) == identity(len(element)):
                return candidate
        raise AssertionError("inverse not found")

    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def conjugate(actor, element):
    def inverse(value):
        candidate = identity(len(value))
        for _ in range(1, 64):
            candidate = multiply(candidate, value)
            if multiply(value, candidate) == identity(len(value)):
                return candidate
        raise AssertionError("inverse not found")

    return multiply(multiply(actor, element), inverse(actor))


def main():
    zero = tuple(tuple(0 for _ in range(3)) for _ in range(3))
    q0 = matrix_unit(0, 0)
    q1 = matrix_unit(1, 1)
    e01 = matrix_unit(0, 1)
    e10 = matrix_unit(1, 0)
    s0 = matrix_unit(0, 2)
    s1 = matrix_unit(1, 2)
    t0 = matrix_unit(2, 0)
    t1 = matrix_unit(2, 1)
    source = matrix_unit(2, 2)
    parent = add(q0, q1)

    s = (s0, s1)
    t = (t0, t1)
    e = ((q0, e01), (e10, q1))

    # Full balanced-cross matrix-unit action table.
    for i in range(2):
        for j in range(2):
            assert multiply(s[i], t[j]) == e[i][j]
            for k in range(2):
                assert multiply(e[i][j], s[k]) == (s[i] if j == k else zero)
                assert multiply(t[k], e[i][j]) == (t[j] if k == i else zero)
                assert multiply(t[i], s[j]) == (source if i == j else zero)

    assert add(q0, q1) == parent
    assert multiply(parent, s0) == s0
    assert multiply(parent, s1) == s1
    assert multiply(t0, parent) == t0
    assert multiply(t1, parent) == t1
    assert add(parent, source) == identity(3)
    assert parent != source

    # Aggregate Morita cell on root coordinates (7,8,9,10) renamed
    # (0,1,2,3).  Coefficient 1 in this scoped occurrence menu is represented
    # by the local range unit `parent`.
    S0 = root(0, 2, s0)
    S1 = root(0, 3, s1)
    T0 = root(2, 1, t0)
    T1 = root(3, 1, t1)
    C0 = root(0, 1, q0)
    C1 = root(0, 1, q1)
    N = root(0, 1, parent)
    D = root(1, 0, parent)
    U0 = root(1, 2, s0)
    U1 = root(1, 3, s1)
    V0 = root(2, 0, t0)
    V1 = root(3, 0, t1)
    R0 = root(1, 0, q0)
    R1 = root(1, 0, q1)
    H = multiply(
        multiply(root(2, 3, identity(3)), root(3, 2, identity(3))),
        root(2, 3, identity(3)),
    )

    assert commutator(S0, T0) == C0
    assert commutator(S1, T1) == C1
    assert multiply(C0, C1) == N
    assert commutator(D, S0) == U0
    assert commutator(D, S1) == U1
    assert commutator(T0, D) == V0
    assert commutator(T1, D) == V1
    assert commutator(U0, V0) == R0
    assert commutator(U1, V1) == R1
    assert multiply(R0, R1) == D
    assert multiply(multiply(N, D), N) == multiply(multiply(D, N), D)

    assert conjugate(H, S0) == root(0, 3, s0)
    assert conjugate(H, S1) == root(0, 2, s1)
    assert conjugate(H, U0) == root(1, 3, s0)
    assert conjugate(H, U1) == root(1, 2, s1)

    positive_01 = commutator(conjugate(H, S0), T1)
    positive_10 = commutator(conjugate(H, S1), T0)
    reverse_01 = commutator(conjugate(H, U0), V1)
    reverse_10 = commutator(conjugate(H, U1), V0)
    assert positive_01 == root(0, 1, e01)
    assert positive_10 == root(0, 1, e10)
    assert reverse_01 == root(1, 0, e01)
    assert reverse_10 == root(1, 0, e10)

    K0 = multiply(multiply(positive_01, reverse_10), positive_01)
    K1 = multiply(multiply(positive_10, reverse_01), positive_10)
    cross_swap = multiply(K0, K1)
    assert multiply(K0, K0) == identity(21)
    assert multiply(K1, K1) == identity(21)
    assert commutator(K0, K1) == identity(21)
    assert conjugate(cross_swap, N) == D
    assert conjugate(cross_swap, D) == N

    # Literal commutator witnesses for e_ij s_k and t_k e_ij, on spare root
    # coordinates 4,5,6.  This validates the stronger full action table, not
    # only the four nonzero identities named in the claim.
    one = identity(21)
    for i in range(2):
        for j in range(2):
            for k in range(2):
                expected_left = root(4, 6, s[i]) if j == k else one
                expected_right = root(4, 6, t[j]) if k == i else one
                assert commutator(root(4, 5, e[i][j]), root(5, 6, s[k])) == expected_left
                assert commutator(root(4, 5, t[k]), root(5, 6, e[i][j])) == expected_right

    assert C1 != identity(21)
    print("exact GL_21(F2) private-middle plus balanced-cross-action Morita model; p != h; marked q1 survives")


if __name__ == "__main__":
    main()
