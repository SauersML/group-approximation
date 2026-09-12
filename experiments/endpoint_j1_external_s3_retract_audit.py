"""Exact q-corner audit for ``<P,J1,x_78(1),x_87(1)>``.

Run only through MSI.  All identities use faithful sparse Leavitt normal
forms; no finite-prefix quotient or numerical tolerance is involved.
"""

from endpoint_chain_center_hecke_collision_audit import coeff, whitehead
from depth_one_paired_leavitt_return_search import equal, multiply as coefficient_multiply
from endpoint_external_s3_retract_audit import (
    corner,
    generated_corner_group,
    power,
    root,
    scalar_projection,
)
from signed_hecke_literal_pauli_probe_audit import matrices_equal, matrix_multiply, word_matrix


def main():
    q = coeff("1", "1")
    assert equal(coefficient_multiply(q, q), q)

    support = scalar_projection(q)
    endpoint = word_matrix(whitehead(8, 2, 2))
    j1 = word_matrix(whitehead(7, 8, 1))
    n = root(7, 8)
    m = root(8, 7)

    for generator in (endpoint, j1, n, m):
        assert matrices_equal(matrix_multiply(support, generator),
                              matrix_multiply(generator, support))
    assert matrices_equal(corner(support, endpoint), support)
    assert matrices_equal(corner(support, j1), support)

    n_corner = corner(support, n)
    m_corner = corner(support, m)
    group = generated_corner_group(support, (n_corner, m_corner))
    assert len(group) == 6
    assert matrices_equal(power(support, n_corner, 2), support)
    assert matrices_equal(power(support, m_corner, 2), support)
    assert matrices_equal(
        power(support, matrix_multiply(n_corner, m_corner), 3), support
    )

    print("q corner", q)
    print("P and J1 corner restrictions are identity", True)
    print("native corner group order", len(group))


if __name__ == "__main__":
    main()
