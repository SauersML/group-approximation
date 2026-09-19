#!/usr/bin/env python3
"""Search compound radius-two slots for H=L=N in the degree-four cover."""

import argparse
import importlib.util
from itertools import product
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-composite-omega-internal-solutions.py")
SPEC = importlib.util.spec_from_file_location("packet", SOURCE)
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)

SEQUENCES = {
    "H": ((0, 0), (1, 1), (2, 2), (1, 3),
          (2, 4), (3, 5), (2, 6), (3, 7)),
    "L": ((0, 7), (1, 0), (2, 1), (3, 2), (2, 3), (3, 4)),
    "N": ((0, 4), (1, 5), (0, 6), (1, 7), (2, 0), (3, 1)),
}


def coefficient_pool():
    representatives = {M.ONE: ()}
    for length in (1, 2):
        for word in M.reduced_words(length):
            representatives.setdefault(M.evaluate(word), word)
    return tuple(sorted(representatives.items(), key=lambda item: item[1]))


def reduce_outer(sequence, slots):
    stack = []
    for copy, slot in sequence:
        unit = slots[slot]
        if unit == M.ONE:
            continue
        if stack and stack[-1][0] == copy:
            unit = M.mul(stack.pop()[1], unit)
            if unit == M.ONE:
                continue
        stack.append((copy, unit))
    return tuple(stack)


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, default=0)
parser.add_argument("--shards", type=int, default=1)
args = parser.parse_args()
assert 0 <= args.shard < args.shards

pool = coefficient_pool()
units = tuple(unit for unit, _ in pool)
names = tuple(word for _, word in pool)
fixed = {2: M.A, 3: M.C, 5: M.B, 6: M.D}
tested = 0
assigned_pairs = 0
for pair_index, (g0, g1) in enumerate(product(range(len(pool)), repeat=2)):
    if pair_index % args.shards != args.shard:
        continue
    assigned_pairs += 1
    for g4, g7 in product(range(len(pool)), repeat=2):
        tested += 1
        slots = dict(fixed)
        slots.update({0: units[g0], 1: units[g1],
                      4: units[g4], 7: units[g7]})
        h_word = reduce_outer(SEQUENCES["H"], slots)
        if (h_word == reduce_outer(SEQUENCES["L"], slots)
                == reduce_outer(SEQUENCES["N"], slots)):
            print("HIT", "indices", (g0, g1, g4, g7),
                  "words", (names[g0], names[g1], names[g4], names[g7]),
                  "H_syllables", len(h_word), flush=True)
            raise SystemExit(42)

print("pool", len(pool))
print("assigned_pairs", assigned_pairs)
print("tested", tested)
print("hits 0")
print("shard", args.shard, args.shards)
