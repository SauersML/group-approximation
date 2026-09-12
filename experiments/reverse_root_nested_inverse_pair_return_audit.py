"""Audit the first non-Boolean return after the actual mixed-braid root.

Run on MSI only.  The prefix calculation proves the literal EL20 return.
The 4-by-4 signed-permutation calculation is a scoped occurrence model:
the returned normalizer can retain a nontrivial chart sign even though the
positive middle root is the identity on the selected source chart.
"""

from depth_one_paired_leavitt_return_search import canonical, signed_l0
from individual_cross_whitehead_one_return_search import (
    full_signed_signature,
    root,
    word_matrix,
)
from support_partial_whitehead_native_return_audit import matrices_equal


def multiply(left, right):
    return tuple(
        tuple(sum(left[i][k] * right[k][j] for k in range(4))
              for j in range(4))
        for i in range(4)
    )


def commutator(left, right):
    # Every displayed generator is an involution.
    return multiply(multiply(multiply(left, right), left), right)


def main():
    one = canonical((("", ""),))
    t0 = canonical((("", "0"),))
    s0 = canonical((("0", ""),))

    # Matrix-root notation: x_ij has row i and column j.  Thus the first
    # argument of root is the source/column and the second the target/row.
    a = (root(7, 9, one),)       # x_97(1), the actual complementary output
    u = (root(5, 7, t0),)        # x_75(t_0)
    v = (root(6, 5, s0),)        # x_56(s_0)
    h = (root(6, 7, one),)       # x_76(1), positive in signed L_0
    n = (root(6, 9, one),)       # x_96(1), external signed normalizer

    uv = u + v + u + v
    ah = a + h + a + h
    nested = a + uv + a + uv
    assert matrices_equal(word_matrix(uv), word_matrix(h))
    assert matrices_equal(word_matrix(ah), word_matrix(n))
    assert matrices_equal(word_matrix(nested), word_matrix(n))

    character = signed_l0()
    assert full_signed_signature(a, character) is None
    assert full_signed_signature(u, character) is None
    assert full_signed_signature(v, character) is None
    assert full_signed_signature(h, character) is not None
    assert full_signed_signature(n, character) is not None

    # Two source charts, each with a two-dimensional reservoir.  A swaps
    # the charts.  U,V are one on the selected chart and a Pauli pair on
    # the other chart.  Hence H=[U,V] is +1 on the source, but
    # N=[A,H] is -1 on it.  This is the surviving external-return gauge.
    identity = (
        (1, 0, 0, 0), (0, 1, 0, 0),
        (0, 0, 1, 0), (0, 0, 0, 1),
    )
    A = (
        (0, 0, 1, 0), (0, 0, 0, 1),
        (1, 0, 0, 0), (0, 1, 0, 0),
    )
    U = (
        (1, 0, 0, 0), (0, 1, 0, 0),
        (0, 0, 0, 1), (0, 0, 1, 0),
    )
    V = (
        (1, 0, 0, 0), (0, 1, 0, 0),
        (0, 0, 1, 0), (0, 0, 0, -1),
    )
    Q = (
        (1, 0, 0, 0), (0, 1, 0, 0),
        (0, 0, 0, 0), (0, 0, 0, 0),
    )
    for involution in (A, U, V):
        assert multiply(involution, involution) == identity
    H = commutator(U, V)
    N = commutator(A, H)
    assert multiply(H, H) == identity
    assert multiply(N, N) == identity
    assert multiply(H, Q) == Q
    assert multiply(Q, H) == Q
    assert multiply(N, Q) == tuple(tuple(-entry for entry in row) for row in Q)
    assert multiply(Q, N) == tuple(tuple(-entry for entry in row) for row in Q)

    print("[x_75(t0),x_56(s0)]=x_76(1), a positive signed root")
    print("[x_97(1),x_76(1)]=x_96(1), an external signed normalizer")
    print("the nested non-Boolean word has exact full signed-source Gram")
    print("the two-chart model retains gauge -1 on that source")


if __name__ == "__main__":
    main()
