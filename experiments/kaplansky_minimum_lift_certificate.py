"""Exact low-weight certificate/search for cross-atlas lifts of s0.

Four fixed units generate the full binary Leavitt unit group.  Among all
additional units in the radius-three atlas ball, this program asks whether
1, 3, or 5 terms can correct their Leavitt evaluation to s0.  If none can,
the displayed seven-term correction is minimum within this finite universe.
The weight-five test is an exact pair/triple meet-in-the-middle computation.
"""

from collections import defaultdict

from depth_one_paired_leavitt_return_search import add
from kaplansky_affine_lift_search import four_generator_atlas
from kaplansky_asymmetric_atlas_search import (
    S0,
    cayley_ball,
    evaluate_sum,
    expanded_terms,
    key,
)


KNOWN_SEVEN = (
    (1, 0),
    (6, 8),
    (0, 2, 9),
    (3, 1, 7),
    (5, 3, 1),
    (5, 3, 4),
    (5, 11, 10),
)


def vectors(columns, target):
    depth = max(
        [len(nu) for value in columns + [target] for _, nu in value],
        default=0,
    )
    expanded = [expanded_terms(value, depth) for value in columns + [target]]
    coordinates = {term for terms in expanded for term in terms}
    coordinate = {term: i for i, term in enumerate(sorted(coordinates))}
    parity_bit = len(coordinate)

    def encode(terms, parity):
        value = parity << parity_bit
        for term in terms:
            value ^= 1 << coordinate[term]
        return value

    return [encode(terms, 1) for terms in expanded[:-1]], encode(expanded[-1], 1)


def find_at_most_five(column_vectors, target):
    n = len(column_vectors)
    by_value = {value: i for i, value in enumerate(column_vectors)}
    if target in by_value:
        return (by_value[target],)

    pairs = defaultdict(list)
    for i in range(n):
        left = column_vectors[i]
        for j in range(i + 1, n):
            pairs[left ^ column_vectors[j]].append((i, j))

    # Weight three = one column plus one disjoint pair.
    for k, value in enumerate(column_vectors):
        for i, j in pairs.get(target ^ value, ()):
            if k != i and k != j:
                return tuple(sorted((i, j, k)))

    # Weight five = one triple plus one disjoint pair.
    for i in range(n):
        if i % 50 == 0:
            print("triple first index", i, "of", n, flush=True)
        vi = column_vectors[i]
        for j in range(i + 1, n):
            vij = vi ^ column_vectors[j]
            for k in range(j + 1, n):
                wanted = target ^ vij ^ column_vectors[k]
                for p, q in pairs.get(wanted, ()):
                    if p not in (i, j, k) and q not in (i, j, k):
                        return tuple(sorted((i, j, k, p, q)))
    return None


def main():
    mandatory = [value for _, value in four_generator_atlas()]
    mandatory_keys = {key(value) for value in mandatory}
    _, ball, words = cayley_ball(3)
    records = [
        (value, word) for value, word in zip(ball, words)
        if key(value) not in mandatory_keys
    ]
    columns = [value for value, _ in records]
    target = add(S0, evaluate_sum(mandatory))
    column_vectors, target_vector = vectors(columns, target)
    found = find_at_most_five(column_vectors, target_vector)
    if found is not None:
        print("CORRECTION_OF_WEIGHT_AT_MOST_FIVE", [records[i][1] for i in found])
        return

    by_word = {word: value for value, word in records}
    correction = evaluate_sum([by_word[word] for word in KNOWN_SEVEN])
    assert key(add(correction, target)) == ()
    print("NO_CORRECTION_OF_WEIGHT_1_3_5")
    print("MINIMUM_CORRECTION_WEIGHT_7")
    print("total exact s0 lift support 11")
    print("seven correction words", KNOWN_SEVEN)


if __name__ == "__main__":
    main()
