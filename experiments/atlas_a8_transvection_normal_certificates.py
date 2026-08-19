#!/usr/bin/env python3
"""Exact six-certificate compression for the A8 collision transvection.

The chart group is GL(4,2)=A8.  The collision 19243 first-chart syllable is
b=I+E_(2,3).  This script proves that the six standard adjacent
transvections generate the full group and that each is a single conjugate of b.
It freezes shortest conjugator words and the directed Cayley diameter in those
six generators.

Everything is exact over F2 and uses only the Python standard library.
"""
from collections import deque

I4 = tuple(tuple(int(i == j) for j in range(4)) for i in range(4))


def mul(a, b):
    return tuple(tuple(
        sum(a[i][k] * b[k][j] for k in range(4)) & 1
        for j in range(4)) for i in range(4))


def inv(a):
    aug = [list(a[i]) + [int(i == j) for j in range(4)] for i in range(4)]
    for col in range(4):
        pivot = next(row for row in range(col, 4) if aug[row][col])
        aug[col], aug[pivot] = aug[pivot], aug[col]
        for row in range(4):
            if row != col and aug[row][col]:
                aug[row] = [x ^ y for x, y in zip(aug[row], aug[col])]
    return tuple(tuple(row[4:]) for row in aug)


def transvection(row, col):
    out = [list(r) for r in I4]
    out[row][col] ^= 1
    return tuple(tuple(r) for r in out)


GENS = (
    ("t01", transvection(0, 1)),
    ("t10", transvection(1, 0)),
    ("t12", transvection(1, 2)),
    ("t21", transvection(2, 1)),
    ("t23", transvection(2, 3)),
    ("t32", transvection(3, 2)),
)
G = dict(GENS)
B = G["t23"]

# Shortest conjugator words found by the exhaustive BFS below.
EXPECTED = {
    "t01": ("t12", "t21", "t10", "t01", "t23", "t32", "t21", "t12"),
    "t10": ("t01", "t10", "t12", "t21", "t10", "t01", "t23", "t32", "t21", "t12"),
    "t12": ("t23", "t32", "t21", "t12"),
    "t21": ("t12", "t21", "t23", "t32", "t21", "t12"),
    "t23": (),
    "t32": ("t23", "t32"),
}


def eval_word(word):
    value = I4
    for name in word:
        value = mul(value, G[name])
    return value


def main():
    # The six adjacent transvections generate all GL(4,2), whose order is 20160.
    words = {I4: ()}
    todo = deque([I4])
    while todo:
        old = todo.popleft()
        for name, generator in GENS:
            new = mul(old, generator)
            if new not in words:
                words[new] = words[old] + (name,)
                todo.append(new)
    assert len(words) == 20160
    diameter = max(len(word) for word in words.values())
    assert diameter == 15

    # Search the entire group for shortest conjugators of b to each standard
    # transvection, then pin the resulting words so later compiler work has a
    # deterministic certificate family rather than an existence statement.
    found = {}
    for target_name, target in GENS:
        best = None
        for conjugator, word in words.items():
            if mul(mul(conjugator, B), inv(conjugator)) == target:
                if best is None or len(word) < len(best):
                    best = word
        assert best is not None
        found[target_name] = best
    assert found == EXPECTED

    for target_name, word in EXPECTED.items():
        conjugator = eval_word(word)
        assert mul(mul(conjugator, B), inv(conjugator)) == G[target_name]

    print("six adjacent transvections generate GL(4,2)=A8, order 20160")
    print("directed Cayley diameter in the six-transvection alphabet: 15")
    for target, word in EXPECTED.items():
        print(
            f"{target} = a t23 a^-1, shortest |a|={len(word)}: "
            f"{' '.join(word) or '1'}"
        )


if __name__ == "__main__":
    main()
