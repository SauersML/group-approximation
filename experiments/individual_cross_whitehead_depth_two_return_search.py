"""Exact depth-two one-occurrence return search for the individual K_i cuts.

Candidates are (a) one elementary root with coefficient s_mu t_nu for
|mu|,|nu|<=2, excluding 1, or (b) the genuine partial Whitehead whose
reverse coefficient is s_nu t_mu.  The h=x_28(1) signature is a first
prefilter; every survivor is checked on the other nine signed-L0 generators.
Run on MSI, never locally.
"""

from itertools import product

from depth_one_paired_leavitt_return_search import (
    ARROWS, INDEX, canonical, constant_transvection, left_elementary,
    right_elementary, signed_l0, to_constant_matrix,
)
from individual_cross_whitehead_one_return_search import (
    BINARY_IDENTITY, J1_WORD, K_WORDS, root, word_matrix,
)


H_INDEX = ARROWS.index((8, 2))
HARD_CAP = 18_000


def words_through_depth_two():
    return ("", "0", "1", "00", "01", "10", "11")


def coeff(mu, nu):
    return canonical(((mu, nu),))


def conjugate_word(factors, generator):
    matrix = constant_transvection(*generator)
    for factor in factors:
        matrix = left_elementary(matrix, *factor)
    for factor in factors:
        matrix = right_elementary(matrix, *factor)
    return matrix


def signed_image(factors, generator_index, character):
    constant = to_constant_matrix(conjugate_word(factors, ARROWS[generator_index]))
    if constant is None:
        return None
    if constant not in character or character[constant] != (generator_index < 3):
        return None
    return constant


def full_signature_after_h(factors, character):
    images = []
    for generator_index in range(len(ARROWS)):
        if generator_index == H_INDEX:
            continue
        image = signed_image(factors, generator_index, character)
        if image is None:
            return None
        images.append(image)
    return tuple(images)


def coefficient_name(pair):
    mu, nu = pair
    if not mu:
        return f"t{nu}"
    if not nu:
        return f"s{mu}"
    return f"s{mu}t{nu}"


def candidate_name(kind, position, pair):
    source, target = position
    forward = coefficient_name(pair)
    if kind == "root":
        return f"x_{target}{source}({forward})"
    reverse = coefficient_name((pair[1], pair[0]))
    return (f"x_{target}{source}({forward}) "
            f"x_{source}{target}({reverse}) "
            f"x_{target}{source}({forward})")


def main():
    character = signed_l0()
    words = words_through_depth_two()
    pairs = tuple((mu, nu) for mu, nu in product(words, repeat=2)
                  if (mu, nu) != ("", ""))
    assert len(pairs) == 48
    positions = tuple((s, t) for s in INDEX for t in INDEX if s != t)

    candidates = []
    for source, target in positions:
        for pair in pairs:
            forward = coeff(*pair)
            candidates.append(("root", (source, target), pair,
                               (root(source, target, forward),)))
            reverse = coeff(pair[1], pair[0])
            candidates.append(("whitehead", (source, target), pair, (
                root(source, target, forward),
                root(target, source, reverse),
                root(source, target, forward),
            )))
    assert len(candidates) == 42 * 48 * 2 == 4032

    tests = 0
    result_counts = {}
    prefilter_counts = {}
    for branch, k_word in enumerate(K_WORDS):
        for target_name, target_prefix in (("Q", ()), ("J1Q", J1_WORD)):
            h_survivors = 0
            hits = []
            for kind, position, pair, candidate in candidates:
                tests += 1
                if tests > HARD_CAP:
                    raise RuntimeError("hard candidate cap exceeded")
                relative = target_prefix + candidate + k_word
                if signed_image(relative, H_INDEX, character) is None:
                    continue
                h_survivors += 1
                if full_signature_after_h(relative, character) is None:
                    continue
                same_k = word_matrix(candidate) == word_matrix(k_word)
                identity_product = (
                    to_constant_matrix(word_matrix(candidate + k_word))
                    == BINARY_IDENTITY
                )
                hits.append((kind, position, pair, same_k, identity_product))
            result_counts[(branch, target_name)] = len(hits)
            prefilter_counts[(branch, target_name)] = h_survivors
            print(f"K_{branch} -> {target_name}: h survivors {h_survivors}, hits {len(hits)}")
            for kind, position, pair, same_k, identity_product in hits:
                print(kind, candidate_name(kind, position, pair),
                      "same_K_matrix", same_k,
                      "identity_product", identity_product)

    print("exact prefix monomials", len(pairs))
    print("candidates per branch/target", len(candidates))
    print("candidate tests", tests)
    print("h-prefilter counts", prefilter_counts)
    assert tests == 16_128
    # Filled from and checked by the exact MSI run; any future menu or result
    # change must be reviewed rather than silently accepted.
    assert result_counts == {
        (0, "Q"): 2, (0, "J1Q"): 0,
        (1, "Q"): 2, (1, "J1Q"): 0,
    }
    assert all(count >= result_counts[key]
               for key, count in prefilter_counts.items())


if __name__ == "__main__":
    main()
