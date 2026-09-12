#!/usr/bin/env python3
"""Search abstract post-pivot relators that reduce to the target commutator."""

import importlib.util
from collections import Counter
from itertools import combinations
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

UNIT = {"1": P.ONE, "a": P.A, "b": P.B, "c": P.C, "d": P.D}
TARGET = P.mul(P.mul(P.mul(P.C, P.D), P.C), P.D)


def multiset_permutations(values):
    counts = Counter(values)
    names = tuple(counts)
    result = [None] * len(values)

    def visit(position):
        if position == len(result):
            yield tuple(result)
            return
        for name in names:
            if counts[name]:
                counts[name] -= 1
                result[position] = name
                yield from visit(position + 1)
                counts[name] += 1

    yield from visit(0)


def reduce_word(signs, corners):
    stack = []

    def append(kind, value):
        if stack and stack[-1][0] == kind:
            old = stack.pop()[1]
            value = old + value if kind == "z" else P.mul(old, value)
        if (kind == "z" and value) or (kind == "D" and value != P.ONE):
            stack.append((kind, value))

    for sign, corner in zip(signs, corners):
        append("z", sign)
        if corner == "X":
            append("z", -1)
        else:
            append("D", UNIT[corner])
    return tuple(stack)


families = (
    ("target", ("c", "c", "d", "d", "X")),
    ("target_pad2", ("c", "c", "d", "d", "1", "1", "X")),
    ("target_pad4", ("c", "c", "d", "d", "1", "1", "1", "1", "X")),
    ("source_target", ("a", "a", "b", "b", "c", "c", "d", "d", "X")),
)
for family, corners in families:
    length = len(corners)
    negative_count = (length - 1) // 2
    tested = 0
    hits = []
    for negative in combinations(range(length), negative_count):
        signs = tuple(-1 if i in negative else 1 for i in range(length))
        for ordering in multiset_permutations(corners):
            tested += 1
            if reduce_word(signs, ordering) == (("D", TARGET),):
                hits.append((signs, ordering))
                if len(hits) <= 20:
                    print("HIT", family, signs, ordering, flush=True)
    print(f"family={family} tested={tested} hits={len(hits)}", flush=True)
