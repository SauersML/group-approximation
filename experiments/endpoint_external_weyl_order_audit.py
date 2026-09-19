"""Exact endpoint/external-Weyl order audit.

Run only through MSI.  Every calculation uses faithful sparse Leavitt normal
forms; there is no finite-prefix quotient and no numerical tolerance.
"""

from endpoint_chain_center_hecke_collision_audit import coeff, entries, whitehead
from signed_hecke_literal_pauli_probe_audit import (
    identity_matrix,
    matrices_equal,
    matrix_multiply,
    word_matrix,
)


IDENTITY = identity_matrix()


def multiply(*matrices):
    answer = IDENTITY
    for matrix in matrices:
        answer = matrix_multiply(answer, matrix)
    return answer


def power(element, exponent):
    answer = IDENTITY
    for _ in range(exponent):
        answer = matrix_multiply(answer, element)
    return answer


def root(target, source):
    one = coeff("", "")
    return word_matrix(((source, target, one),))


def main():
    endpoint = word_matrix(whitehead(8, 2, 2))
    n = root(7, 8)
    m = root(8, 7)
    native_weyl = multiply(n, m, n)

    products = (
        multiply(endpoint, n),
        multiply(endpoint, m),
        multiply(endpoint, native_weyl),
    )
    asserted_orders = (4, 4, 6)
    for product, order in zip(products, asserted_orders):
        assert matrices_equal(power(product, order), IDENTITY)
        for proper_divisor in range(1, order):
            if order % proper_divisor == 0:
                assert not matrices_equal(power(product, proper_divisor), IDENTITY)

    endpoint_n_endpoint = multiply(endpoint, n, endpoint)
    endpoint_m_endpoint = multiply(endpoint, m, endpoint)

    print("orders endpoint*n, endpoint*m, endpoint*w", asserted_orders)
    print("endpoint*n*endpoint", entries(endpoint_n_endpoint))
    print("endpoint*m*endpoint", entries(endpoint_m_endpoint))


if __name__ == "__main__":
    main()
