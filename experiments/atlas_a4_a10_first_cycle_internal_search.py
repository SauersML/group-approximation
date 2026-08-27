#!/usr/bin/env python3
"""Search A10 for the first post-carrier core involution."""

import json
import argparse
from collections import deque
from itertools import permutations


def perm(values):
    return tuple(value - 1 for value in values)


def mul(left, right):
    return tuple(left[right[index]] for index in range(len(left)))


def inv(value):
    result = [0] * len(value)
    for source, target in enumerate(value):
        result[target] = source
    return tuple(result)


def power(value, exponent):
    result = tuple(range(len(value)))
    for _ in range(exponent):
        result = mul(result, value)
    return result


def subgroup_order(generators):
    identity = tuple(range(len(generators[0])))
    seen = {identity}
    todo = [identity]
    while todo:
        old = todo.pop()
        for generator in generators:
            new = mul(old, generator)
            if new not in seen:
                seen.add(new)
                todo.append(new)
    return len(seen)


R = perm([1, 3, 5, 6, 2, 7, 4, 8, 9, 10])
Z = perm([1, 3, 5, 7, 2, 4, 6, 8, 9, 10])
C = perm([1, 4, 6, 2, 7, 3, 5, 8, 10, 9])
T = perm([1, 2, 5, 4, 9, 7, 10, 8, 3, 6])
S = perm([2, 1, 3, 8, 9, 6, 10, 4, 5, 7])
IDENTITY = tuple(range(10))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient", choices=("a10", "s10"), default="a10")
    args = parser.parse_args()
    candidates = []
    if args.ambient == "a10":
        generators = (R, Z, C, T, S)
        seen = {IDENTITY}
        todo = deque([IDENTITY])

        def elements():
            while todo:
                old = todo.popleft()
                yield old
                for generator in generators:
                    new = mul(old, generator)
                    if new not in seen:
                        seen.add(new)
                        todo.append(new)
    else:
        seen = None

        def elements():
            yield from permutations(range(10))

    tested = 0
    for old in elements():
        tested += 1
        if (power(old, 2) == IDENTITY
                and mul(old, Z) == mul(Z, old)
                and mul(old, C) == mul(C, old)
                and mul(mul(old, R), old) == inv(R)):
            for y_name, y in (("t", T), ("t^-1", inv(T))):
                if power(mul(old, y), 3) == IDENTITY:
                    candidates.append({
                        "u": [value + 1 for value in old],
                        "y": y_name,
                        "F_u_order": subgroup_order((R, Z, C, old)),
                        "u_y_order": subgroup_order((old, y)),
                    })
    expected = 1_814_400 if args.ambient == "a10" else 3_628_800
    assert tested == expected
    print(json.dumps({
        "ambient": args.ambient.upper(),
        "ambient_order": tested,
        "candidate_count": len(candidates),
        "candidates": candidates,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
