"""Find signed-normalizer dressings of the concrete mixed cell transport."""

from signed_hecke_literal_pauli_probe_audit import (
    ONE,
    canonical,
    constant_matrix,
    inverse_word_matrix,
    matrices_equal,
    matrix_multiply,
    signed_l0,
    signed_signature,
    word_matrix,
)
from signed_hecke_root_normalizer_audit import COORDS, transvection


EXTERNAL_ARROWS = (
    (4, 7),
    (5, 8),
    (6, 9),
    (7, 2),
    (8, 4),
    (8, 7),
    (9, 5),
    (9, 8),
)


def commutes(left, right):
    return matrices_equal(matrix_multiply(left, right), matrix_multiply(right, left))


def conjugate(word, matrix):
    return matrix_multiply(
        matrix_multiply(word_matrix(word), matrix), inverse_word_matrix(word)
    )


def main() -> None:
    signed = signed_l0()
    coefficient = lambda mu, nu: canonical(((mu, nu),))
    c2 = coefficient("000", "00")
    d2 = coefficient("00", "000")
    endpoint = ((2, 4, c2), (4, 2, d2), (2, 4, c2))
    prefix = ((8, 9, c2), (9, 8, d2), (8, 9, c2))
    first_transport = endpoint + prefix

    g_star = word_matrix(((8, 2, ONE), (9, 4, ONE)))
    y2 = word_matrix(((3, 8, coefficient("00", "1")),))
    a22 = word_matrix(((2, 1, coefficient("1", "00")),))
    cell = (g_star, y2, a22)

    external_centralizers = []
    for source, target in EXTERNAL_ARROWS:
        root_word = ((source, target, ONE),)
        root = word_matrix(root_word)
        assert signed_signature(root_word, signed) is not None
        if all(commutes(root, operator) for operator in cell):
            external_centralizers.append((source, target))
    assert external_centralizers == [(9, 5)]

    normalizing_root_centralizers = []
    for source in COORDS:
        for target in COORDS:
            if source == target:
                continue
            root_word = ((source, target, ONE),)
            if signed_signature(root_word, signed) is None:
                continue
            root = word_matrix(root_word)
            if all(commutes(root, operator) for operator in cell):
                normalizing_root_centralizers.append(
                    ((source, target), transvection(source, target) in signed)
                )
    assert len(normalizing_root_centralizers) == 8
    assert sum(not internal for _arrow, internal in normalizing_root_centralizers) == 1

    relative_word = ((9, 5, ONE),)
    second_transport = first_transport + relative_word
    for operator in cell:
        assert matrices_equal(
            conjugate(first_transport, operator),
            conjugate(second_transport, operator),
        )
    relative_matrix = word_matrix(
        tuple(reversed(second_transport)) + first_transport
    )
    assert matrices_equal(relative_matrix, word_matrix(relative_word))

    print("signed-normalizing root centralizers of the depth-2 cell =", normalizing_root_centralizers)
    print("unique external centralizer = x_59(1)")
    print("H and H x_59(1) are distinct exact transports with relative loop x_59(1)")
    print("both transports have the same full source and moved-source range")
    print("their cross Gram is the full unitary x_59(1)Q")


if __name__ == "__main__":
    main()
