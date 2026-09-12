"""Exact range-support audit for the endpoint/J1/B2 enlargement.

Run only through MSI.  It verifies in faithful Leavitt normal form that each
nonidentity matrix coefficient lies in ``pR`` while ``q`` survives modulo
``pR``.
"""

from endpoint_chain_center_hecke_collision_audit import coeff, whitehead
from depth_one_paired_leavitt_return_search import add, equal, multiply
from endpoint_external_s3_retract_audit import generated_corner_group
from signed_hecke_literal_pauli_probe_audit import (
    COORDS,
    INDEX,
    matrices_equal,
    matrix_multiply,
    word_matrix,
    zero_matrix,
)


def root(target, source, coefficient):
    return word_matrix(((source, target, coefficient),))


def deviations(matrix):
    one = coeff("", "")
    for row in range(len(COORDS)):
        for column in range(len(COORDS)):
            expected = one if row == column else frozenset()
            deviation = add(matrix[row][column], expected)
            if deviation:
                yield deviation


def active_projection(value):
    matrix = zero_matrix()
    matrix[INDEX[7]][INDEX[7]] = value
    matrix[INDEX[8]][INDEX[8]] = value
    return matrix


def main():
    p = coeff("0", "0")
    q = coeff("1", "1")
    b2 = coeff("00", "1")
    a2 = coeff("1", "00")
    b3 = coeff("000", "1")
    assert not multiply(p, q)
    assert not multiply(q, p)

    j2 = word_matrix(whitehead(8, 9, 2))
    a2_root = root(5, 8, a2)
    b3_root = root(9, 5, b3)
    singer = matrix_multiply(matrix_multiply(j2, b3_root), a2_root)
    range_named = {
        "P": word_matrix(whitehead(8, 2, 2)),
        "J1": word_matrix(whitehead(7, 8, 1)),
        "J2": j2,
        "B2": root(8, 4, b2),
    }
    counts = {}
    for name, matrix in range_named.items():
        delta = tuple(deviations(matrix))
        assert delta
        assert all(equal(multiply(p, coefficient), coefficient)
                   for coefficient in delta)
        counts[name] = len(delta)

    support = active_projection(q)
    corner_named = dict(range_named)
    corner_named.update({"A2": a2_root, "B3": b3_root, "M": singer})
    for name, matrix in corner_named.items():
        left = matrix_multiply(support, matrix)
        right = matrix_multiply(matrix, support)
        assert matrices_equal(left, support), name
        assert matrices_equal(right, support), name

    n = root(7, 8, coeff("", ""))
    m = root(8, 7, coeff("", ""))
    n_corner = matrix_multiply(matrix_multiply(support, n), support)
    m_corner = matrix_multiply(matrix_multiply(support, m), support)
    group = generated_corner_group(support, (n_corner, m_corner))
    assert len(group) == 6

    # q cannot lie in pR: if q=pr, then pq=q, contradicting pq=0 and q!=0.
    assert q
    print("pR-supported deviation counts", counts)
    print("q survives modulo pR", True)
    print("active q-corner kills P,J1,J2,B2,A2,B3,M", True)
    print("active q-corner native group order", len(group))


if __name__ == "__main__":
    main()
