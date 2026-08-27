"""Exact common-middle typing and source-return audit for the mixed braid.

Run on MSI only.  This extends the complementary partial-Whitehead table by
the already authenticated signed-Hecke typing of its two middle roots.
"""

from depth_one_paired_leavitt_return_search import (
    canonical, signed_l0,
)
from individual_cross_whitehead_one_return_search import (
    coeff, full_signed_signature, root, word_matrix,
)
from support_partial_whitehead_native_return_audit import matrices_equal


Q0 = canonical((("0", "0"),))
Q1 = canonical((("1", "1"),))


def partial(projection):
    a = root(7, 9, coeff("", ""))
    b = root(9, 7, projection)
    return (a, b, a)


def actual_partial(projection):
    # Ordered (7,9) block L(projection)U(1)L(projection).
    return (
        root(7, 9, projection),
        root(9, 7, coeff("", "")),
        root(7, 9, projection),
    )


def main():
    character = signed_l0()
    one = coeff("", "")
    r = coeff("1", "0")
    b0 = (root(9, 7, Q0),)                 # x_79(q_0)
    b1 = (root(9, 7, Q1),)                 # x_79(q_1)
    n = (root(9, 7, one),)                 # x_79(1) in positive L_0
    symmetric_A = partial(Q1)
    symmetric_B = partial(Q0)
    A = actual_partial(Q1)
    B = actual_partial(Q0)

    # The two middle roots preserve the signed source and fuse to the
    # positive constant generator.  Therefore their restrictions to Q agree.
    assert full_signed_signature(b0, character) is not None
    assert full_signed_signature(b1, character) is not None
    assert full_signed_signature(n, character) is not None
    assert matrices_equal(word_matrix(b0 + b1), word_matrix(n))

    # Reconstruct the relative mixed-braid word L=GK_0 and its exposed
    # factorization L=x_89(r)A.
    p = coeff("0", "1")
    u = root(8, 7, p)
    v = root(7, 8, r)
    up = root(9, 7, one)
    vp = root(7, 9, Q1)
    aggregate_first = (u, up)
    aggregate_second = (v, vp)
    G = aggregate_first + aggregate_second + aggregate_first
    K = (u, v, u)
    L = G + K
    x = (root(9, 8, r),)                  # x_89(r)
    assert matrices_equal(word_matrix(L), word_matrix(x + A))
    assert not matrices_equal(word_matrix(L), word_matrix(x + symmetric_A))
    assert not matrices_equal(word_matrix(L), word_matrix(symmetric_A + x))

    # The true complementary cell has the same asymmetric spelling.  Its
    # braid with A returns the constant reverse root x_97(1), not either
    # support-idempotent Whitehead asserted by the symmetric audit.
    reverse_constant = (root(7, 9, one),)
    assert matrices_equal(word_matrix(A + B + A),
                          word_matrix(reverse_constant))
    assert matrices_equal(word_matrix(B + A + B),
                          word_matrix(reverse_constant))
    assert full_signed_signature(reverse_constant, character) is None
    assert not matrices_equal(word_matrix(A + B + A),
                              word_matrix(symmetric_A + symmetric_B + symmetric_A))

    print("b0 and b1 preserve signed Q and b0*b1=x_79(1) positive")
    print("L=x_89(r) A_actual with A_actual=L(q1)U(1)L(q1)")
    print("the symmetric partial used by the complementary-support audit is not A_actual")
    print("A_actual B_actual A_actual=B_actual A_actual B_actual=x_97(1)")


if __name__ == "__main__":
    main()
