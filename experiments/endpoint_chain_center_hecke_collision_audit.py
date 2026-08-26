"""Exact audit of endpoint Whitehead placements against center-chain flags.

Run on MSI only.  The first target is the chain (7,8,2), whose second
Whitehead is expected to preserve the quarter flag and move the extra
eighth-scale generator.
"""

from itertools import product

from depth_one_paired_leavitt_return_search import binary_words, canonical, equal
from signed_hecke_literal_pauli_probe_audit import (
    COORDS, INDEX, identity_matrix, inverse_word_matrix, matrix_key,
    matrix_multiply, matrices_equal, word_matrix,
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


def right_depth(matrix):
    return max((len(nu) for row in matrix for entry in row for _, nu in entry),
               default=0)


GROUP_CACHE = {}


def group_lookup(label, group, matrix):
    depth = max(3, right_depth(matrix))
    cache_key = (label, depth)
    if cache_key not in GROUP_CACHE:
        GROUP_CACHE[cache_key] = {
            fixed_key([list(row) for row in key], depth): sign
            for key, sign in group.items()
        }
    return GROUP_CACHE[cache_key].get(fixed_key(matrix, depth))


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
                  "inH", group_lookup("H", h, image) is not None,
                  "inK1", group_lookup("K1", k1, image) is not None,
                  "inK2", group_lookup("K2", k2, image) is not None)

        generator_names = {
            "H": ("C1", "C2", "C3"),
            "K1": ("C1", "C2", "C3", "v", "w"),
            "K2": ("C1", "C2", "C3", "v", "w", "s"),
        }
        for label, group in (("H", h), ("K1", k1), ("K2", k2)):
            images = tuple(
                conjugate(word, named[name])
                for name in generator_names[label]
            )
            signs = tuple(group_lookup(label, group, image) for image in images)
            normalized = all(sign is not None for sign in signs)
            character_preserved = normalized and all(
                sign == name.startswith("C")
                for sign, name in zip(signs, generator_names[label])
            )
            # Each Whitehead is an involution, so inclusion of the generated
            # subgroup already implies equality.
            print(" ", label, "normalized", normalized,
                  "signed", character_preserved)

    groups = {"H": h, "K1": k1, "K2": k2}
    generator_names = {
        "H": ("C1", "C2", "C3"),
        "K1": ("C1", "C2", "C3", "v", "w"),
        "K2": ("C1", "C2", "C3", "v", "w", "s"),
    }

    def profile(r, s_coord, m):
        word = whitehead(r, s_coord, m)
        a_m = coeff("1", "0" * m)
        a_next = coeff("1", "0" * (m + 1))
        b_m = coeff("0" * m, "1")
        b_next = coeff("0" * (m + 1), "1")
        legal = (
            matrices_equal(conjugate(word, root(1, r, a_m)),
                           root(1, s_coord, a_next))
            and matrices_equal(conjugate(word, root(r, 3, b_m)),
                               root(s_coord, 3, b_next))
        )
        result = []
        for label in ("H", "K1", "K2"):
            images = tuple(
                conjugate(word, named[name])
                for name in generator_names[label]
            )
            group = groups[label]
            signs = tuple(group_lookup(label, group, image) for image in images)
            normalized = all(sign is not None for sign in signs)
            signed = normalized and all(
                sign == name.startswith("C")
                for sign, name in zip(signs, generator_names[label])
            )
            result.append(signed)
        return legal, tuple(result)

    allowed = tuple(c for c in COORDS if c not in (1, 3))
    print("legal oriented edge profiles (H,K1,K2)")
    edge_profiles = {}
    for m in (1, 2):
        for r in allowed:
            for s_coord in allowed:
                if r == s_coord:
                    continue
                legal, status = profile(r, s_coord, m)
                if legal:
                    edge_profiles[(r, s_coord, m)] = status
                    print((r, s_coord, m), status)

    print("legal chains ending at detector endpoint 2 or 4")
    useful = []
    for r3 in (2, 4):
        for r2 in allowed:
            for r1 in allowed:
                if len({r1, r2, r3}) != 3:
                    continue
                first = edge_profiles[(r1, r2, 1)]
                second = edge_profiles[(r2, r3, 2)]
                if (first[0] and second[0]
                        and ((first[1] and not first[2])
                             or (second[1] and not second[2]))):
                    useful.append(((r1, r2, r3), first, second))
    print("H-preserving chains with a K1-preserving/K2-ejecting edge =",
          len(useful))
    for item in useful:
        print(item)

    # For the prioritized second edge, identify the exact fine-flag
    # intersection after conjugation.
    w2 = whitehead(8, 2, 2)
    s_prime = conjugate(w2, named["s"])
    k2_prime = generated_signed(tuple(
        (named[name] if name != "s" else s_prime, name.startswith("C"))
        for name in ("C1", "C2", "C3", "v", "w", "s")
    ))
    join = generated_signed(tuple(
        (named[name], name.startswith("C"))
        for name in ("C1", "C2", "C3", "v", "w", "s")
    ) + ((s_prime, False),))
    intersection = set(k2).intersection(k2_prime)
    assert all(k2[key] == k2_prime[key] for key in intersection)
    print("prioritized K2,K2',intersection,join orders =",
          len(k2), len(k2_prime), len(intersection), len(join))
    print("intersection equals K1 =", intersection == set(k1))


if __name__ == "__main__":
    main()
