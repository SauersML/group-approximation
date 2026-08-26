"""Exact audit of endpoint Whitehead placements against center-chain flags.

Run on MSI only.  The first target is the chain (7,8,2), whose second
Whitehead is expected to preserve the quarter flag and move the extra
eighth-scale generator.
"""

from itertools import product

from depth_one_paired_leavitt_return_search import binary_words, canonical, equal
from signed_hecke_literal_pauli_probe_audit import (
    COORDS, INDEX, identity_matrix, inverse_word_matrix, matrix_key,
    matrix_multiply, word_matrix,
)


def coeff(mu, nu):
    return canonical(((mu, nu),))


def root(i, j, coefficient):
    return word_matrix(((j, i, coefficient),))


def whitehead(r, s, m):
    c = coeff("0" * (m + 1), "0" * m)
    d = coeff("0" * m, "0" * (m + 1))
    return ((r, s, c), (s, r, d), (r, s, c))


def conjugate(word, matrix):
    w = word_matrix(word)
    winv = inverse_word_matrix(word)
    return matrix_multiply(matrix_multiply(w, matrix), winv)


def entries(matrix):
    answer = []
    for row, i in enumerate(COORDS):
        for column, j in enumerate(COORDS):
            expected = coeff("", "") if i == j else ()
            if not equal(matrix[row][column], expected):
                answer.append((i, j, matrix[row][column]))
    return answer


def fixed_key(matrix, depth=3):
    rows = []
    for row in matrix:
        normalized = []
        for entry in row:
            assert all(len(nu) <= depth for _, nu in entry)
            normalized.append(canonical(
                (mu + suffix, nu + suffix)
                for mu, nu in entry
                for suffix in binary_words(depth - len(nu))
            ))
        rows.append(tuple(normalized))
    return tuple(rows)


def generated_signed(generators):
    """Return the finite generated group as matrix-key -> generator parity."""
    identity = identity_matrix()
    seen = {fixed_key(identity): 0}
    frontier = [identity]
    while frontier:
        current = frontier.pop()
        current_sign = seen[fixed_key(current)]
        for generator, sign in generators:
            nxt = matrix_multiply(current, generator)
            key = fixed_key(nxt)
            nxt_sign = current_sign ^ sign
            if key in seen:
                assert seen[key] == nxt_sign
            else:
                seen[key] = nxt_sign
                frontier.append(nxt)
    return seen


def main():
    q = coeff("1", "1")
    a1, a2 = coeff("1", "0"), coeff("1", "00")
    named = {
        "C1": root(4, 2, q),
        "C2": root(5, 4, q),
        "C3": root(6, 5, q),
        "v": root(5, 7, a1),
        "w": root(6, 7, a1),
        "s": root(6, 8, a2),
        "A1": root(4, 7, a1),
        "A2": root(5, 8, a2),
    }
    h = generated_signed(tuple((named[name], 1) for name in ("C1", "C2", "C3")))
    k1 = generated_signed(tuple((named[name], name.startswith("C"))
                                for name in ("C1", "C2", "C3", "v", "w")))
    k2 = generated_signed(tuple((named[name], name.startswith("C"))
                                for name in ("C1", "C2", "C3", "v", "w", "s")))
    print("orders H,K1,K2 =", len(h), len(k1), len(k2))

    chain = ((7, 8, 1), (8, 2, 2))
    for r, s_coord, m in chain:
        word = whitehead(r, s_coord, m)
        print("whitehead", (r, s_coord, m))
        for name, matrix in named.items():
            image = conjugate(word, matrix)
            print(" ", name, entries(image),
                  "inH", fixed_key(image) in h,
                  "inK1", fixed_key(image) in k1,
                  "inK2", fixed_key(image) in k2)

        generator_names = {
            "H": ("C1", "C2", "C3"),
            "K1": ("C1", "C2", "C3", "v", "w"),
            "K2": ("C1", "C2", "C3", "v", "w", "s"),
        }
        for label, group in (("H", h), ("K1", k1), ("K2", k2)):
            images = tuple(
                fixed_key(conjugate(word, named[name]))
                for name in generator_names[label]
            )
            normalized = all(image in group for image in images)
            character_preserved = normalized and all(
                group[image] == name.startswith("C")
                for image, name in zip(images, generator_names[label])
            )
            # Each Whitehead is an involution, so inclusion of the generated
            # subgroup already implies equality.
            print(" ", label, "normalized", normalized,
                  "signed", character_preserved)


if __name__ == "__main__":
    main()
