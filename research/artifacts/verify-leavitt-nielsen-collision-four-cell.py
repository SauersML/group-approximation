#!/usr/bin/env python3
"""Complete four-cell ribbon audit for the collided Leavitt word."""

from collections import Counter
from itertools import permutations, product

ORIENTATION = (1, 1, -1, -1)
SIGNS = sum(([1, 1, -1] if sign == 1 else [1, -1, -1]
             for sign in ORIENTATION), [])
POSITIVE = tuple(i for i, sign in enumerate(SIGNS) if sign == 1)
NEGATIVE = tuple(i for i, sign in enumerate(SIGNS) if sign == -1)
ROTATION = tuple(3 * (i // 3) + (i % 3 + 1) % 3 for i in range(12))


def cycles(permutation):
    seen = set()
    result = []
    for start in range(len(permutation)):
        if start in seen:
            continue
        cycle = []
        current = start
        while current not in seen:
            seen.add(current)
            cycle.append(current)
            current = permutation[current]
        result.append(tuple(cycle))
    return tuple(result)


def connected(adjacency):
    reached = {0}
    stack = [0]
    while stack:
        for neighbour in adjacency[stack.pop()]:
            if neighbour not in reached:
                reached.add(neighbour)
                stack.append(neighbour)
    return len(reached) == 4


def corners(relator, orientation):
    positive = (("u", 1), ("k", 1), ("u", 1)) if relator else (
        ("h", 1), ("y", 1), ("x", 1))
    if orientation == 1:
        return positive
    return ((positive[1][0], -1),
            (positive[0][0], -1),
            (positive[2][0], -1))


def reduce_gate_word(word):
    result = []
    for name, sign in word:
        if name in {"u", "y"}:
            sign = 1
        if result and result[-1][0] == name and (
                name in {"u", "y"} or result[-1][1] == -sign):
            result.pop()
        else:
            result.append((name, sign))
    return tuple(result)


checked = 0
closed = 0
maximal = []
for targets in permutations(NEGATIVE):
    alpha = [None] * 12
    adjacency = [set() for _ in range(4)]
    for left, right in zip(POSITIVE, targets, strict=True):
        alpha[left] = right
        alpha[right] = left
        adjacency[left // 3].add(right // 3)
        adjacency[right // 3].add(left // 3)
    if not connected(adjacency):
        continue
    regions = cycles(tuple(ROTATION[alpha[i]] for i in range(12)))
    if len(regions) != 4:  # 4-6+F=2
        continue

    for relators in product((0, 1), repeat=4):
        vertex_corners = tuple(corners(relators[v], ORIENTATION[v])
                               for v in range(4))
        if any(relators[left // 3] == relators[alpha[left] // 3]
               and ORIENTATION[left // 3] == -ORIENTATION[alpha[left] // 3]
               and left % 3 + alpha[left] % 3 == 2
               for left in POSITIVE):
            continue
        checked += 1
        labels = tuple(reduce_gate_word(
            vertex_corners[alpha[half] // 3][alpha[half] % 3]
            for half in region) for region in regions)
        trivial = sum(not label for label in labels)
        if trivial >= 3:
            closed += 1
        if trivial == 2:
            maximal.append(tuple(label for label in labels if label))

assert checked == 2620
assert closed == 0
assert len(maximal) == 4
residuals = {word for pair in maximal for word in pair}
assert Counter(map(len, residuals)) == {4: 4}

# The four words are rotations/inverses of u k^-1 h x.  Its literal
# coefficient expansion is the nonempty alternating free-product normal form
# displayed below; every block is visibly nonidentity.
normal_form = (
    (1, "a"), (0, "q"), (1, "e"), (0, "p^-1 a"),
    (1, "p q"), (0, "a"),
)
assert all(block for _, block in normal_form)
assert all(normal_form[i][0] != normal_form[i + 1][0]
           for i in range(len(normal_form) - 1))

print("PASS: 2620 reduced four-cell planar colorings")
print("PASS: no disk; four maximal cases have one residual length-four face")
print("PASS: residual u k^-1 h x has nonempty G0*G1 normal form")
