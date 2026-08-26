"""Exact complementary partial-Whitehead braid audit.

Run on MSI only.  This tests the first continuation of the mixed-braid
relative word W_79(1,q_1) by its complementary q_0 cell.
"""

from depth_one_paired_leavitt_return_search import (
    ONE, canonical, signed_l0,
)
from individual_cross_whitehead_one_return_search import (
    full_signed_signature, root, word_matrix,
)
from support_partial_whitehead_native_return_audit import matrices_equal


Q0 = canonical((("0", "0"),))
Q1 = canonical((("1", "1"),))


def partial(projection):
    return (
        root(7, 9, ONE),
        root(9, 7, projection),
        root(7, 9, ONE),
    )


def supported(projection):
    return (
        root(7, 9, projection),
        root(9, 7, projection),
        root(7, 9, projection),
    )


def main():
    character = signed_l0()
    w0 = partial(Q0)
    w1 = partial(Q1)
    braid_left = w1 + w0 + w1
    braid_right = w0 + w1 + w0
    support0 = supported(Q0)
    support1 = supported(Q1)
    full = supported(ONE)

    assert matrices_equal(word_matrix(braid_left), word_matrix(support0))
    assert matrices_equal(word_matrix(braid_right), word_matrix(support1))
    assert matrices_equal(word_matrix(support0 + support1), word_matrix(full))

    for name, word in (
        ("W(q0)", w0),
        ("W(q1)", w1),
        ("W(q1)W(q0)", w1 + w0),
        ("W(q0)W(q1)", w0 + w1),
        ("support q0", support0),
        ("support q1", support1),
        ("full support product", support0 + support1),
    ):
        print(name, "preserves signed Q", full_signed_signature(word, character) is not None)


if __name__ == "__main__":
    main()
