#!/usr/bin/env python3
"""Exact minimal transvection generating cycle for GL(4,2)=A8.

The collision 19243 opcode is t23=I+E_(2,3).  The directed four-cycle

    t01, t12, t23, t30

generates the whole chart group.  The script freezes its exact Cayley diameter
and shortest conjugators carrying t23 to the other three cycle edges.

The matching mathematical lower bound (three transvections always have a
common nonzero fixed vector in dimension four) is recorded in Cairn.
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
    ("t23", transvection(2, 3)),
    ("t01", transvection(0, 1)),
    ("t12", transvection(1, 2)),
    ("t30", transvection(3, 0)),
)
G = dict(GENS)
B = G["t23"]
EXPECTED = {
    "t23": (),
    "t01": ("t12", "t30", "t23", "t12", "t30", "t01", "t12", "t30"),
    "t12": ("t01", "t30", "t23", "t30", "t01", "t12", "t01", "t30"),
    "t30": ("t01", "t12", "t23", "t12", "t01", "t30", "t01", "t12"),
}


def eval_word(word):
    value = I4
    for name in word:
        value = mul(value, G[name])
    return value


def main():
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
    assert diameter == 17

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
        a = eval_word(word)
        assert mul(mul(a, B), inv(a)) == G[target_name]

    print("t01,t12,t23,t30 generate GL(4,2)=A8, order 20160")
    print("directed Cayley diameter: 17")
    for target, word in EXPECTED.items():
        print(
            f"{target} = a t23 a^-1, shortest |a|={len(word)}: "
            f"{' '.join(word) or '1'}"
        )


if __name__ == "__main__":
    main()
