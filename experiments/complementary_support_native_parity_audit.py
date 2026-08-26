"""Exact parity/closure audit for the complementary support-return cell.

Run on MSI only.  Tests whether all exact relations among the exposed
partial Whitehead, its complement, and the native J1 still admit a sign on
the exposed occurrence.
"""

from collections import deque

from complementary_partial_whitehead_braid_audit import Q0, Q1, partial
from depth_one_paired_leavitt_return_search import canonical, signed_l0
from individual_cross_whitehead_one_return_search import (
    full_signed_signature, root, word_matrix,
)
from support_chart_union_third_pair_audit import faithful_matrix_key
from support_partial_whitehead_native_return_audit import matrix_multiply


X1 = canonical((("00", "0"),))
Y1 = canonical((("0", "00"),))
J1 = (
    root(7, 8, X1),
    root(8, 7, Y1),
    root(7, 8, X1),
)


def main():
    generator_words = (partial(Q1), partial(Q0), J1)
    generators = tuple(map(word_matrix, generator_words))
    generator_parity = (1, 0, 0)
    identity = word_matrix(())
    key = faithful_matrix_key(identity)
    seen = {key: (identity, 0, ())}
    queue = deque(((identity, 0, ()),))
    parity_collision = None
    cap = 250_000

    while queue:
        current, parity, word = queue.popleft()
        for index, generator in enumerate(generators):
            successor = matrix_multiply(current, generator)
            successor_parity = parity ^ generator_parity[index]
            successor_word = word + (index,)
            successor_key = faithful_matrix_key(successor)
            old = seen.get(successor_key)
            if old is not None:
                if old[1] != successor_parity:
                    parity_collision = (old[2], successor_word)
                    queue.clear()
                    break
                continue
            seen[successor_key] = (successor, successor_parity, successor_word)
            queue.append((successor, successor_parity, successor_word))
            if len(seen) >= cap:
                queue.clear()
                break

    print("closure size/capped", len(seen), len(seen) < cap)
    print("exposed-A parity collision", parity_collision)

    def expanded(word):
        return tuple(factor for index in word for factor in generator_words[index])

    character = signed_l0()
    normalizers = []
    native_targets = []
    for matrix, parity, word in seen.values():
        factors = expanded(word)
        assert faithful_matrix_key(word_matrix(factors)) == faithful_matrix_key(matrix)
        if full_signed_signature(factors, character) is not None:
            normalizers.append((parity, word))
        if full_signed_signature(J1 + factors, character) is not None:
            native_targets.append((parity, word))
    print("signed-Q normalizers by parity", normalizers)
    print("J1Q targets by parity", native_targets)


if __name__ == "__main__":
    main()
