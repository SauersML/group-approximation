"""Exact coefficient-sensitive native-arm diamonds for the reverse returns.

Run on MSI only.  The two diamonds use literal native center-chain arms and
uncancelled Leavitt ``s``/``t`` coefficients; they are not part of the
constant/Boolean external-return census.
"""

from depth_one_paired_leavitt_return_search import equal
from individual_cross_whitehead_one_return_search import (
    J1_WORD,
    coeff,
    root,
    word_matrix,
)


def commutator(left, right):
    """Word for [left,right]; every word below is an involutory root."""
    return tuple(left) + tuple(right) + tuple(left) + tuple(right)


def matrices_equal(left, right):
    return all(
        equal(left[row][column], right[row][column])
        for row in range(len(left))
        for column in range(len(left))
    )


def same_word_matrix(left, right):
    return matrices_equal(word_matrix(left), word_matrix(right))


def check_diamond(A, B, J, U, D, U_prime, V, N):
    C = commutator(U, A)
    D_prime = commutator(B, V)

    # The two coefficient-sensitive factorizations return the same constant
    # spectator root.
    assert same_word_matrix(commutator(C, D), N)
    assert same_word_matrix(commutator(U_prime, D_prime), N)

    # They are the two sides of one literal native Whitehead diamond.
    assert same_word_matrix(J + C + J, U_prime)
    assert same_word_matrix(J + D + J, D_prime)
    assert same_word_matrix(J + N + J, N)


def main():
    one = coeff("", "")

    # Row 1: native arms A_1=x_47(s_1t_0), B_2=x_84(s_00t_1),
    # spectator return N_1=x_96(1).
    A1 = (root(7, 4, coeff("1", "0")),)
    B2 = (root(4, 8, coeff("00", "1")),)
    U1 = (root(4, 9, coeff("", "1")),)       # x_94(t_1)
    D1 = (root(6, 7, coeff("0", "")),)       # x_76(s_0)
    U1_prime = (root(8, 9, coeff("", "00")),)  # x_98(t_00)
    V1 = (root(6, 4, coeff("1", "")),)       # x_46(s_1)
    N1 = (root(6, 9, one),)                   # x_96(1)
    check_diamond(A1, B2, J1_WORD, U1, D1, U1_prime, V1, N1)

    # Row 2 is the next-prefix copy.
    A2 = (root(8, 5, coeff("1", "00")),)
    B3 = (root(5, 9, coeff("000", "1")),)
    J2 = (
        root(8, 9, coeff("000", "00")),
        root(9, 8, coeff("00", "000")),
        root(8, 9, coeff("000", "00")),
    )
    U2 = (root(5, 2, coeff("", "1")),)       # x_25(t_1)
    D2 = (root(7, 8, coeff("00", "")),)      # x_87(s_00)
    U2_prime = (root(9, 2, coeff("", "000")),)  # x_29(t_000)
    V2 = (root(7, 5, coeff("1", "")),)       # x_57(s_1)
    N2 = (root(7, 2, one),)                   # x_27(1)
    check_diamond(A2, B3, J2, U2, D2, U2_prime, V2, N2)

    print("row 1: two native-arm factorizations return x_96(1)")
    print("row 2: two native-arm factorizations return x_27(1)")
    print("each pair is exchanged by its literal prefix Whitehead")


if __name__ == "__main__":
    main()
