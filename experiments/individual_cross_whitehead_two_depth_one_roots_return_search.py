"""Exact two-additional-root return search after the individual K_i words.

Both added occurrences are individually nonnormal depth-one elementary
roots and use genuinely different actor root positions.  The exposed
h=x_28(1) signed image is checked first; only survivors receive the other
nine full signed-L0 checks.  Run on MSI, never locally.
"""

from depth_one_paired_leavitt_return_search import (
    COEFFICIENTS, INDEX, canonical, root_normalizes, signed_l0,
    to_constant_matrix,
)
from individual_cross_whitehead_one_return_search import (
    BINARY_IDENTITY, J1_WORD, K_WORDS, root, word_matrix,
)
from individual_cross_whitehead_depth_two_return_search import (
    H_INDEX, full_signature_after_h, signed_image,
)


HARD_CAP = 400_000


def coeff_name(pair):
    mu, nu = pair
    if not mu:
        return f"t{nu}"
    if not nu:
        return f"s{mu}"
    return f"s{mu}t{nu}"


def root_name(item, pair):
    source, target, _ = item
    return f"x_{target}{source}({coeff_name(pair)})"


def main():
    character = signed_l0()
    positions = tuple((s, t) for s in INDEX for t in INDEX if s != t)
    roots = []
    for position in positions:
        for pair in COEFFICIENTS:
            item = root(position[0], position[1], canonical((pair,)))
            if not root_normalizes(item, character):
                roots.append((position, pair, item))
    assert len(roots) == 304
    active_positions = {position for position, _, _ in roots}
    assert len(active_positions) == 38

    pairs = tuple(
        (first, second)
        for first in roots
        for second in roots
        if first[0] != second[0]
    )
    assert len(pairs) == 38 * 37 * 8 * 8 == 89_984

    tests = 0
    prefilter_counts = {}
    result_counts = {}
    for branch, k_word in enumerate(K_WORDS):
        for target_name, target_prefix in (("Q", ()), ("J1Q", J1_WORD)):
            h_survivors = 0
            h_examples = []
            hits = []
            for first, second in pairs:
                tests += 1
                if tests > HARD_CAP:
                    raise RuntimeError("hard ordered-pair cap exceeded")
                candidate = (first[2], second[2])
                relative = target_prefix + candidate + k_word
                if signed_image(relative, H_INDEX, character) is None:
                    continue
                h_survivors += 1
                h_examples.append((first, second))
                if full_signature_after_h(relative, character) is None:
                    continue
                constant_product = to_constant_matrix(word_matrix(candidate + k_word))
                identity_product = constant_product == BINARY_IDENTITY
                hits.append((first, second, constant_product is not None,
                             identity_product))
            prefilter_counts[(branch, target_name)] = h_survivors
            result_counts[(branch, target_name)] = len(hits)
            print(f"K_{branch} -> {target_name}: h survivors {h_survivors}, hits {len(hits)}")
            for first, second, constant_product, identity_product in hits[:40]:
                print(root_name(first[2], first[1]), root_name(second[2], second[1]),
                      "constant_product", constant_product,
                      "identity_product", identity_product)
            for first, second in h_examples:
                print("h-only candidate",
                      root_name(first[2], first[1]), root_name(second[2], second[1]))

    print("individually nonnormal roots", len(roots))
    print("different active root positions", len(active_positions))
    print("ordered different-position pairs per branch/target", len(pairs))
    print("candidate tests", tests)
    print("h-prefilter counts", prefilter_counts)
    print("result counts", result_counts)
    assert tests == 359_936
    assert prefilter_counts == {
        (0, "Q"): 1, (0, "J1Q"): 0,
        (1, "Q"): 1, (1, "J1Q"): 0,
    }
    assert result_counts == {
        (0, "Q"): 0, (0, "J1Q"): 0,
        (1, "Q"): 0, (1, "J1Q"): 0,
    }


if __name__ == "__main__":
    main()
