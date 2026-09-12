"""MITM search: one unmatched depth-one Whitehead plus one nonnormal root.

Both occurrence orders are tested, with different oriented root positions.
First-occurrence words are grouped by the exact Leavitt-matrix image of
h=x_28(1); only distinct states are crossed with the second menu.  Every
expanded h-survivor receives the other nine full signed-L0 checks.
Run on MSI, never locally.
"""

from collections import defaultdict

from depth_one_paired_leavitt_return_search import (
    ARROWS, COEFFICIENTS, INDEX, ONE, ZERO, add, canonical, constant_transvection,
    multiply, root_normalizes, signed_l0,
)
from individual_cross_whitehead_one_return_search import (
    J1_WORD, K_WORDS, root, word_matrix,
)
from individual_cross_whitehead_depth_two_return_search import (
    H_INDEX, full_signature_after_h, signed_image,
)


HARD_COMPRESSED_TRANSITION_CAP = 2_000_000
HARD_EXPANDED_SURVIVOR_CAP = 100_000


def matrix_key(matrix):
    return tuple(tuple(row) for row in matrix)


def key_matrix(key):
    return [list(row) for row in key]


def conjugate_matrix(matrix, factors):
    answer = [row[:] for row in matrix]
    for factor in factors:
        source, target, coefficient = factor
        updated = [row[:] for row in answer]
        for column in range(7):
            updated[INDEX[target]][column] = add(
                updated[INDEX[target]][column],
                multiply(coefficient, answer[INDEX[source]][column]),
            )
        for row in range(7):
            updated[row][INDEX[source]] = add(
                updated[row][INDEX[source]],
                multiply(updated[row][INDEX[target]], coefficient),
            )
        answer = updated
    return answer


def constant_ring_matrix(binary_matrix):
    return [
        [ONE if (binary_matrix[row] >> column) & 1 else ZERO
         for column in range(7)]
        for row in range(7)
    ]


def coeff_name(pair):
    mu, nu = pair
    if not mu:
        return f"t{nu}"
    if not nu:
        return f"s{mu}"
    return f"s{mu}t{nu}"


def word_name(descriptor):
    kind, position, pairs, word = descriptor
    del kind, position
    names = []
    for item, pair in zip(word, pairs):
        source, target, _ = item
        names.append(f"x_{target}{source}({coeff_name(pair)})")
    return " ".join(names)


def group_first_states(start_matrix, candidates):
    grouped = defaultdict(list)
    for descriptor in candidates:
        grouped[matrix_key(conjugate_matrix(start_matrix, descriptor[3]))].append(descriptor)
    return grouped


def main():
    character = signed_l0()
    positions = tuple((s, t) for s in INDEX for t in INDEX if s != t)
    coefficients = tuple((pair, canonical((pair,))) for pair in COEFFICIENTS)

    roots = []
    for position in positions:
        for pair, coefficient in coefficients:
            word = (root(position[0], position[1], coefficient),)
            if not root_normalizes(word[0], character):
                roots.append(("root", position, (pair,), word))
    assert len(roots) == 304

    whiteheads = []
    for position in positions:
        for forward_pair, forward in coefficients:
            for reverse_pair, reverse in coefficients:
                word = (
                    root(position[0], position[1], forward),
                    root(position[1], position[0], reverse),
                    root(position[0], position[1], forward),
                )
                whiteheads.append((
                    "whitehead", position,
                    (forward_pair, reverse_pair, forward_pair), word,
                ))
    assert len(whiteheads) == 2688

    conceptual_per_order = len(whiteheads) * len(roots) - 38 * 64 * 8
    assert conceptual_per_order == 797_696

    h = constant_transvection(*ARROWS[H_INDEX])
    starts = {
        "Q": h,
        "J1Q": conjugate_matrix(h, J1_WORD),
    }
    positive_l0 = tuple(matrix for matrix, sign in character.items() if not sign)
    assert len(positive_l0) == 4096
    target_sets = tuple(
        {
            matrix_key(conjugate_matrix(constant_ring_matrix(matrix), k_word))
            for matrix in positive_l0
        }
        for k_word in K_WORDS
    )
    assert all(len(target_set) == 4096 for target_set in target_sets)
    orders = (
        ("WR", whiteheads, roots),
        ("RW", roots, whiteheads),
    )

    grouped_cache = {}
    projected = 0
    for target_name, start in starts.items():
        for order_name, first_menu, second_menu in orders:
            grouped = group_first_states(start, first_menu)
            grouped_cache[(target_name, order_name)] = grouped
            transitions = len(grouped) * len(second_menu)
            projected += transitions
            print(target_name, order_name,
                  "first words", len(first_menu),
                  "unique h states", len(grouped),
                  "compressed transitions", transitions)
    print("projected shared compressed transitions", projected)
    if projected > HARD_COMPRESSED_TRANSITION_CAP:
        raise RuntimeError("compressed transition hard cap exceeded before traversal")

    compressed = 0
    expanded = 0
    result_counts = {}
    h_counts = {}
    for target_name, target_prefix in (("Q", ()), ("J1Q", J1_WORD)):
        for order_name, first_menu, second_menu in orders:
            del first_menu
            grouped = grouped_cache[(target_name, order_name)]
            h_survivors_by_branch = {0: [], 1: []}
            hits_by_branch = {0: [], 1: []}
            for state_key, first_descriptors in grouped.items():
                state = key_matrix(state_key)
                for second in second_menu:
                    compressed += 1
                    after_second = conjugate_matrix(state, second[3])
                    after_second_key = matrix_key(after_second)
                    for branch, k_word in enumerate(K_WORDS):
                        if after_second_key not in target_sets[branch]:
                            continue
                        for first in first_descriptors:
                            if first[1] == second[1]:
                                continue
                            expanded += 1
                            if expanded > HARD_EXPANDED_SURVIVOR_CAP:
                                raise RuntimeError("expanded h-survivor hard cap exceeded")
                            descriptors = (first, second)
                            candidate = first[3] + second[3]
                            relative = target_prefix + candidate + k_word
                            # Recheck the exact exposed row after descriptor expansion.
                            assert signed_image(relative, H_INDEX, character) is not None
                            h_survivors_by_branch[branch].append(descriptors)
                            if full_signature_after_h(relative, character) is not None:
                                assert target_name == "Q" and order_name == "WR"
                                assert word_matrix(first[3]) == word_matrix(k_word)
                                allowed_pairs = (
                                    {("1", ""), ("1", "0"), ("1", "1")}
                                    if branch == 0 else
                                    {("0", ""), ("0", "0"), ("0", "1")}
                                )
                                assert second[1] in {(6, 8), (9, 8)}
                                assert second[2][0] in allowed_pairs
                                hits_by_branch[branch].append(descriptors)
            for branch in range(2):
                h_survivors = h_survivors_by_branch[branch]
                hits = hits_by_branch[branch]
                key = (target_name, order_name, branch)
                h_counts[key] = len(h_survivors)
                result_counts[key] = len(hits)
                print(key, "expanded h survivors", len(h_survivors),
                      "full hits", len(hits))
                for first, second in h_survivors[:30]:
                    print(" h", word_name(first), "+", word_name(second))
                for first, second in hits[:30]:
                    print(" HIT", word_name(first), "+", word_name(second))

    print("conceptual candidates per order/branch/target", conceptual_per_order)
    print("compressed transitions executed", compressed)
    print("expanded h survivors", expanded)
    print("h counts", h_counts)
    print("full result counts", result_counts)
    assert projected == compressed == 1_128_560
    assert expanded == 1700
    assert h_counts == {
        ("Q", "WR", 0): 426, ("Q", "WR", 1): 426,
        ("Q", "RW", 0): 424, ("Q", "RW", 1): 424,
        ("J1Q", "WR", 0): 0, ("J1Q", "WR", 1): 0,
        ("J1Q", "RW", 0): 0, ("J1Q", "RW", 1): 0,
    }
    assert result_counts == {
        ("Q", "WR", 0): 12, ("Q", "WR", 1): 12,
        ("Q", "RW", 0): 0, ("Q", "RW", 1): 0,
        ("J1Q", "WR", 0): 0, ("J1Q", "WR", 1): 0,
        ("J1Q", "RW", 0): 0, ("J1Q", "RW", 1): 0,
    }


if __name__ == "__main__":
    main()
