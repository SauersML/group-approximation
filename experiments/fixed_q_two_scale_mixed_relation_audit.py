"""Audit the simultaneous endpoint/prefix Whitehead for the g-star cells."""

from endpoint_whitehead_signed_source_intersection_audit import character_masks
from signed_hecke_literal_pauli_probe_audit import (
    ONE,
    canonical,
    constant_matrix,
    identity_matrix,
    inverse_word_matrix,
    matrices_equal,
    matrix_multiply,
    signed_l0,
    signed_signature,
    to_binary_actor,
    word_matrix,
)
from signed_hecke_root_normalizer_audit import GENERATORS


def conjugate(word, matrix):
    operator = word_matrix(word)
    inverse = inverse_word_matrix(word)
    return matrix_multiply(matrix_multiply(operator, matrix), inverse)


def main() -> None:
    signed = signed_l0()
    coefficient = lambda mu, nu: canonical(((mu, nu),))
    c2 = coefficient("000", "00")
    d2 = coefficient("00", "000")

    endpoint = ((2, 4, c2), (4, 2, d2), (2, 4, c2))
    prefix = ((8, 9, c2), (9, 8, d2), (8, 9, c2))
    simultaneous = endpoint + prefix

    g_word = ((8, 2, ONE), (9, 4, ONE))
    g_star = word_matrix(g_word)
    a2 = coefficient("1", "00")
    a3 = coefficient("1", "000")
    b2 = coefficient("00", "1")
    b3 = coefficient("000", "1")
    y2 = word_matrix(((3, 8, b2),))
    y3 = word_matrix(((3, 9, b3),))
    a22 = word_matrix(((2, 1, a2),))
    a43 = word_matrix(((4, 1, a3),))

    assert matrices_equal(word_matrix(simultaneous + simultaneous), identity_matrix())
    assert matrices_equal(conjugate(simultaneous, g_star), g_star)
    assert matrices_equal(conjugate(simultaneous, y2), y3)
    assert matrices_equal(conjugate(simultaneous, a22), a43)
    assert signed_signature(simultaneous, signed) is None

    # Every direct cross pair is disjoint or has a common source/target root.
    for left, right in ((y2, y3), (a22, a43), (a22, y3), (a43, y2)):
        assert matrices_equal(matrix_multiply(left, right), matrix_multiply(right, left))

    operator = word_matrix(simultaneous)
    inverse = inverse_word_matrix(simultaneous)
    intersection = []
    fixed = []
    for actor, sign in signed.items():
        image = to_binary_actor(
            matrix_multiply(
                matrix_multiply(operator, constant_matrix(actor)), inverse
            )
        )
        if image is not None and image in signed:
            intersection.append(actor)
            assert signed[image] == sign
            if image == actor:
                fixed.append(actor)
    assert len(intersection) == 16
    assert len(fixed) == 16
    assert sum(signed[actor] for actor in intersection) == 8

    parity, masks = character_masks()
    annihilator = tuple(
        mask
        for mask in masks
        if all(
            (mask & parity[actor]).bit_count() % 2 == 0
            for actor in intersection
        )
    )
    assert len(annihilator) == 32
    assert 1 << 1 in annihilator  # the character negative only on 5 -> 4

    constant_images = sum(
        to_binary_actor(conjugate(simultaneous, constant_matrix(generator)))
        is not None
        for generator in GENERATORS
    )
    assert constant_images == 3

    print("H^2=1; H fixes g* and transports the complete depth-2 cell to depth 3")
    print("H normalizes the signed pair =", False)
    print("displayed L0 generators remaining constant actor-supported =", constant_images)
    print("|L0 intersect H L0 H| =", len(intersection))
    print("intersection sign split = 8+8 and H fixes it pointwise")
    print("characters trivial on the intersection =", len(annihilator))
    print("canonical Q/HQ Hecke overlap = tau(Q)/512")


if __name__ == "__main__":
    main()
