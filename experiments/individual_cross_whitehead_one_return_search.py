"""Exact capped search for one low-depth occurrence returning K_iQ.

Run on MSI, never locally.  Every hit is checked on all ten signed-L0
generators, not only on h=x_28(1).
"""

from depth_one_paired_leavitt_return_search import (
    ARROWS, COEFFICIENTS, COEFFICIENT_NAMES, INDEX,
    canonical, constant_transvection, identity_matrix, left_elementary,
    right_elementary, signed_l0, to_constant_matrix,
)

H_INDEX = ARROWS.index((8, 2))
HARD_CAP = 20_000
BINARY_IDENTITY = tuple(1 << index for index in range(7))


def coeff(mu, nu):
    return canonical(((mu, nu),))


def root(source, target, coefficient):
    return (source, target, coefficient)


P, R = coeff("0", "1"), coeff("1", "0")
X1, Y1 = coeff("00", "0"), coeff("0", "00")
K_WORDS = (
    (root(8, 7, P), root(7, 8, R), root(8, 7, P)),
    (root(8, 7, R), root(7, 8, P), root(8, 7, R)),
)
J1_WORD = (root(7, 8, X1), root(8, 7, Y1), root(7, 8, X1))


def conjugate_word(factors, generator):
    matrix = constant_transvection(*generator)
    for factor in factors:
        matrix = left_elementary(matrix, *factor)
    for factor in factors:
        matrix = right_elementary(matrix, *factor)
    return matrix


def word_matrix(factors):
    matrix = identity_matrix()
    for factor in reversed(factors):
        matrix = left_elementary(matrix, *factor)
    return matrix


def full_signed_signature(factors, character):
    order = (H_INDEX,) + tuple(i for i in range(len(ARROWS)) if i != H_INDEX)
    images = []
    for generator_index in order:
        constant = to_constant_matrix(conjugate_word(factors, ARROWS[generator_index]))
        if constant is None:
            return None
        if constant not in character or character[constant] != (generator_index < 3):
            return None
        images.append(constant)
    return tuple(images)


def coefficient_name(element):
    monomial = next(iter(element))
    return COEFFICIENT_NAMES.get(monomial, f"s{monomial[0]}t{monomial[1]}")


def word_name(word):
    return " ".join(
        f"x_{target}{source}({coefficient_name(coefficient)})"
        for source, target, coefficient in word
    )


def main():
    character = signed_l0()
    positions = tuple((s, t) for s in INDEX for t in INDEX if s != t)
    coefficients = tuple(canonical((item,)) for item in COEFFICIENTS)
    candidates = []
    for source, target in positions:
        for coefficient in coefficients:
            candidates.append(("root", (root(source, target, coefficient),)))
        for forward in coefficients:
            for reverse in coefficients:
                candidates.append(("whitehead", (
                    root(source, target, forward),
                    root(target, source, reverse),
                    root(source, target, forward),
                )))
    assert len(candidates) == 3024

    tests = 0
    result_counts = {}
    for branch, k_word in enumerate(K_WORDS):
        for target_name, target_prefix in (("Q", ()), ("J1Q", J1_WORD)):
            hits = []
            for kind, candidate in candidates:
                tests += 1
                if tests > HARD_CAP:
                    raise RuntimeError("hard full-signature cap exceeded")
                relative = target_prefix + candidate + k_word
                signature = full_signed_signature(relative, character)
                if signature is None:
                    continue
                same_matrix = word_matrix(candidate) == word_matrix(k_word)
                identity_product = (
                    to_constant_matrix(word_matrix(candidate + k_word))
                    == BINARY_IDENTITY
                )
                hits.append((kind, candidate, same_matrix, identity_product,
                             candidate == k_word))
            result_counts[(branch, target_name)] = len(hits)
            print(f"K_{branch} -> {target_name}: hits {len(hits)}")
            for kind, candidate, same_matrix, identity_product, tautological in hits[:40]:
                print(kind, word_name(candidate),
                      "same_K_matrix", same_matrix,
                      "identity_product", identity_product,
                      "tautological", tautological)
            if target_name == "Q":
                assert len(hits) == 2
                assert all(kind == "whitehead" for kind, *_ in hits)
                assert all(same_matrix and identity_product
                           for _, _, same_matrix, identity_product, _ in hits)
            else:
                assert not hits
    print("candidates per branch/target", len(candidates))
    print("simultaneous full-L0 signature tests", tests)
    assert tests == 12_096
    assert result_counts == {
        (0, "Q"): 2, (0, "J1Q"): 0,
        (1, "Q"): 2, (1, "J1Q"): 0,
    }


if __name__ == "__main__":
    main()
