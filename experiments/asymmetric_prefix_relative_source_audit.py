"""Audit the extended asymmetric prefix unit against the full signed source.

Run only through the MSI wrapper.  All coefficient arithmetic uses faithful
binary-prefix normal forms.  The script compares conjugation by

    G = (7 8 9) diag(1,...,u_7,u_8,u^-2_9)

with conjugation by ``A=J1 J2`` on every displayed generator of ``L0`` and
on the two extra quarter-source signs ``r,l``.
"""

from depth_one_paired_leavitt_return_search import (
    ONE,
    ZERO,
    canonical,
    equal,
    multiply as coefficient_multiply,
)
from signed_hecke_literal_pauli_probe_audit import (
    COORDS,
    INDEX,
    identity_matrix,
    matrices_equal,
    matrix_multiply,
    word_matrix,
)


def coeff(left, right):
    return canonical(((left, right),))


def root(row, column, coefficient):
    return (column, row, coefficient)


def diagonal(entries):
    matrix = [[ZERO for _ in COORDS] for _ in COORDS]
    for coordinate in COORDS:
        matrix[INDEX[coordinate]][INDEX[coordinate]] = entries.get(coordinate, ONE)
    return matrix


def permutation(images):
    matrix = [[ZERO for _ in COORDS] for _ in COORDS]
    for coordinate in COORDS:
        image = images.get(coordinate, coordinate)
        matrix[INDEX[image]][INDEX[coordinate]] = ONE
    return matrix


def conjugate(actor, actor_inverse, matrix):
    return matrix_multiply(matrix_multiply(actor, matrix), actor_inverse)


def main():
    q = coeff("1", "1")
    a1, a2, a3 = (coeff("1", "0" * depth) for depth in (1, 2, 3))
    b1, b2, b3 = (coeff("0" * depth, "1") for depth in (1, 2, 3))
    x1, y1 = coeff("00", "0"), coeff("0", "00")
    x2, y2 = coeff("000", "00"), coeff("00", "000")

    u = canonical((("00", "0"), ("01", "10"), ("1", "11")))
    u_inverse = canonical((("0", "00"), ("10", "01"), ("11", "1")))
    u2 = coefficient_multiply(u, u)
    u_inverse2 = coefficient_multiply(u_inverse, u_inverse)
    assert equal(coefficient_multiply(u, u_inverse), ONE)
    assert equal(coefficient_multiply(u_inverse, u), ONE)

    j1_word = (root(8, 7, x1), root(7, 8, y1), root(8, 7, x1))
    j2_word = (root(9, 8, x2), root(8, 9, y2), root(9, 8, x2))
    j1, j2 = word_matrix(j1_word), word_matrix(j2_word)
    actor = matrix_multiply(j1, j2)
    actor_inverse = matrix_multiply(j2, j1)

    d = diagonal({7: u, 8: u, 9: u_inverse2})
    d_inverse = diagonal({7: u_inverse, 8: u_inverse, 9: u2})
    cycle = permutation({7: 8, 8: 9, 9: 7})
    cycle_inverse = permutation({7: 9, 8: 7, 9: 8})
    g = matrix_multiply(cycle, d)
    g_inverse = matrix_multiply(d_inverse, cycle_inverse)
    identity = identity_matrix()
    assert matrices_equal(matrix_multiply(g, g_inverse), identity)
    assert matrices_equal(matrix_multiply(g_inverse, g), identity)
    assert matrices_equal(conjugate(g, g_inverse, j1), j2)

    named = {
        "C3": root(6, 5, q),
        "C2": root(5, 4, q),
        "C1": root(4, 2, q),
        "d": root(8, 2, b2),
        "f": root(9, 4, b3),
        "k": root(9, 2, b3),
        "c": root(9, 7, coefficient_multiply(b3, a1)),
        "v": root(5, 7, a1),
        "w": root(6, 7, a1),
        "s": root(6, 8, a2),
        "r": root(5, 8, a2),
        "l": root(6, 9, a3),
    }
    expected_g_images = {
        "C3": root(6, 5, q),
        "C2": root(5, 4, q),
        "C1": root(4, 2, q),
        "d": root(9, 2, b3),
        "f": root(7, 4, b1),
        "k": root(7, 2, b1),
        "c": root(7, 8, y1),
        "v": root(5, 8, a2),
        "w": root(6, 8, a2),
        "s": root(6, 9, a3),
        "r": root(5, 9, a3),
        "l": root(6, 7, a1),
    }

    failures = []
    for name, generator in named.items():
        source = word_matrix((generator,))
        g_image = conjugate(g, g_inverse, source)
        actor_image = conjugate(actor, actor_inverse, source)
        expected = word_matrix((expected_g_images[name],))
        assert matrices_equal(g_image, expected), name
        same = matrices_equal(g_image, actor_image)
        print(name, "G image equals (J1 J2) image", same, flush=True)
        if not same:
            failures.append(name)

    relative = matrix_multiply(actor_inverse, g)
    relative_inverse = matrix_multiply(g_inverse, actor)
    assert matrices_equal(matrix_multiply(relative, relative_inverse), identity)
    fixed = []
    for name, generator in named.items():
        source = word_matrix((generator,))
        is_fixed = matrices_equal(
            conjugate(relative, relative_inverse, source), source
        )
        fixed.append(name) if is_fixed else None
        print(name, "fixed by R=(J1 J2)^-1 G", is_fixed, flush=True)

    print("comparison failures", tuple(failures), flush=True)
    print("relative fixed generators", tuple(fixed), flush=True)


if __name__ == "__main__":
    main()
