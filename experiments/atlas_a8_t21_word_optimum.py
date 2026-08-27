#!/usr/bin/env python3
"""Exact finite audit of the four-cycle word bound for t21 in GL(4,2).

The established atlas transfer uses the four directed transvections
    t01,t12,t23,t30
and one length-eight word for t21.  This script checks that length eight is
minimal, that no length-nine word reaches t21, and that every length-eight word
has count vector (2,0,2,4).  Consequently the symmetric word-telescoping plus
Cauchy constant 24 cannot be improved by choosing a different positive word.

The arithmetic is dependency-free and exact over F2.  A 4x4 matrix is stored as
four four-bit row masks.
"""

import itertools
import json
from collections import deque


I4 = (1, 2, 4, 8)


def transvection(row, col):
    out = list(I4)
    out[row] ^= 1 << col
    return tuple(out)


def mul(a, b):
    out = []
    for row in a:
        image = 0
        for k in range(4):
            if (row >> k) & 1:
                image ^= b[k]
        out.append(image)
    return tuple(out)


NAMES = ("t01", "t12", "t23", "t30")
T = (
    transvection(0, 1),
    transvection(1, 2),
    transvection(2, 3),
    transvection(3, 0),
)
TARGET = transvection(2, 1)


def cayley_distances():
    dist = {I4: 0}
    queue = deque([I4])
    while queue:
        g = queue.popleft()
        for s in T:
            h = mul(g, s)
            if h not in dist:
                dist[h] = dist[g] + 1
                queue.append(h)
    return dist


def reaches_at_exact_length(length):
    frontier = {I4}
    for _ in range(length):
        frontier = {mul(g, s) for g in frontier for s in T}
    return TARGET in frontier


def shortest_count_vectors(length):
    vectors = set()
    words = 0
    for word in itertools.product(range(4), repeat=length):
        value = I4
        counts = [0, 0, 0, 0]
        for letter in word:
            value = mul(value, T[letter])
            counts[letter] += 1
        if value == TARGET:
            words += 1
            vectors.add(tuple(counts))
    return words, sorted(vectors)


def minimum_square_sum(total, slots=4):
    # Convexity: distribute the total as evenly as possible.
    q, r = divmod(total, slots)
    return r * (q + 1) ** 2 + (slots - r) * q**2


def main():
    dist = cayley_distances()
    assert len(dist) == 20160
    assert max(dist.values()) == 17
    assert dist[TARGET] == 8

    number, vectors = shortest_count_vectors(8)
    assert number == 4
    assert vectors == [(2, 0, 2, 4)]
    assert not reaches_at_exact_length(9)

    shortest_square_sum = sum(x * x for x in vectors[0])
    assert shortest_square_sum == 24
    # Any other positive word has length at least ten.  Even before imposing
    # the group relation, four nonnegative integer counts summing to ten have
    # square-sum at least 26, and the minimum only grows with total length.
    assert minimum_square_sum(10) == 26 > shortest_square_sum

    print(json.dumps({
        "generated_group_order": len(dist),
        "directed_cayley_diameter": max(dist.values()),
        "t21_shortest_length": dist[TARGET],
        "t21_length_8_words": number,
        "t21_length_8_count_vectors": [dict(zip(NAMES, v)) for v in vectors],
        "t21_has_length_9_word": False,
        "shortest_count_square_sum": shortest_square_sum,
        "minimum_count_square_sum_at_length_10": minimum_square_sum(10),
        "conclusion": "24 is globally optimal for positive-word telescoping plus symmetric Cauchy",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
