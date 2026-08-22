#!/usr/bin/env python3
"""Exact sparse Leavitt search around the D8 three-winner near packet."""

import argparse
import hashlib
import importlib.util
from itertools import combinations, product
from pathlib import Path

SOURCE = Path(__file__).with_name("search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def mul_pair(left, right):
    return P.mul(left[0], right[0]), P.mul(right[1], left[1])


def pair(*units):
    value, inverse = P.ONE, P.ONE
    for unit, unit_inverse in units:
        value = P.mul(value, unit)
        inverse = P.mul(unit_inverse, inverse)
    return value, inverse


ONE = (P.ONE, P.ONE)
ROT = pair((P.C, P.C), (P.D, P.D))
ROT_INV = (ROT[1], ROT[0])
REF = (P.C, P.C)
LIBRARY = {
    "1": ONE, "A": ROT, "A-": ROT_INV, "S": REF,
    "a": (P.A, P.A), "c": (P.C, P.C), "e": (P.E, P.E),
    "r": (P.R, P.RINV), "r-": (P.RINV, P.R),
    "p": (P.P, P.PINV), "p-": (P.PINV, P.P),
    "q": (P.Q, P.Q), "b": (P.B, P.B), "d": (P.D, P.D),
}
NAMES = tuple(LIBRARY)
PARADOXICAL = frozenset(("a", "e", "r", "r-", "p", "p-", "q", "b", "d"))


def reduce_fp(factors):
    stack = []
    for copy, value in factors:
        if value[0] == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            value = mul_pair(stack.pop()[1], value)
            if value[0] == P.ONE:
                continue
        stack.append((copy, value))
    return tuple(stack)


def inverse_fp(word):
    return tuple((copy, (value[1], value[0])) for copy, value in reversed(word))


def corner(slots, data):
    return reduce_fp((copy, slots[index]) for copy, index in data)


H_DATA = ((0, 9), (1, 10), (2, 11), (1, 12), (2, 13), (3, 0),
          (2, 1), (1, 2), (0, 3), (1, 4), (2, 5), (1, 6),
          (2, 7), (3, 8))
A0_DATA = ((3, 1), (2, 2), (1, 3), (2, 4), (3, 5), (2, 6), (3, 7))
B0_DATA = ((0, 8), (1, 9), (2, 10), (3, 11), (2, 12), (3, 13))
C0_DATA = ((0, 0),)
A1_DATA = ((3, 3),)
B1_DATA = ((0, 4), (1, 5), (0, 6), (1, 7), (2, 8), (3, 9))
C1_DATA = ((0, 10), (1, 11), (0, 12), (1, 13), (2, 0), (1, 1), (0, 2))
E_DATA = (
    ((3, 2), (2, 3), (3, 4)), ((0, 5),), ((3, 6),),
    ((0, 7), (1, 8), (2, 9), (3, 10)), ((0, 11),),
    ((3, 12),), ((0, 13), (1, 0), (0, 1)),
)


def evaluate(slots):
    h = corner(slots, H_DATA)
    a0, b0, c0 = (corner(slots, x) for x in (A0_DATA, B0_DATA, C0_DATA))
    a1, b1, c1 = (corner(slots, x) for x in (A1_DATA, B1_DATA, C1_DATA))
    e1, e2, e3, e4, e5, e6, e7 = (corner(slots, x) for x in E_DATA)
    rhs0 = reduce_fp(inverse_fp(e7) + h + inverse_fp(e6) + inverse_fp(h)
                     + inverse_fp(e5) + h)
    rhs2 = reduce_fp(inverse_fp(a1) + inverse_fp(h))
    rhs4 = reduce_fp(inverse_fp(e3) + inverse_fp(h) + inverse_fp(e2) + h
                     + inverse_fp(e1) + inverse_fp(h))
    if reduce_fp(h + a0) != rhs0 or reduce_fp(inverse_fp(h) + c0) != rhs2:
        return None
    if reduce_fp(inverse_fp(h) + c1) != rhs4:
        return None
    boundary = reduce_fp(inverse_fp(h) + b0 + inverse_fp(h) + b1
                         + inverse_fp(h) + e4)
    return boundary


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, default=0)
parser.add_argument("--shards", type=int, default=1)
parser.add_argument("--support", type=int, default=3)
args = parser.parse_args()

base_names = ["1"] * 14
base_names[2] = base_names[4] = base_names[5] = base_names[7] = "S"
base_names[8], base_names[9] = "A-", "A"
mutable = tuple(index for index in range(14) if index not in (0, 3))
tested = carriers = 0
for support in range(1, args.support + 1):
    for positions in combinations(mutable, support):
        for names in product(NAMES, repeat=support):
            digest = hashlib.blake2b(repr((positions, names)).encode(),
                                     digest_size=8).digest()
            key = int.from_bytes(digest, "little") % args.shards
            if key != args.shard or not PARADOXICAL.intersection(names):
                continue
            if all(base_names[position] == name for position, name in zip(positions, names)):
                continue
            slot_names = list(base_names)
            for position, name in zip(positions, names):
                slot_names[position] = name
            slots = tuple(LIBRARY[name] for name in slot_names)
            tested += 1
            boundary = evaluate(slots)
            if boundary is None:
                continue
            carriers += 1
            if len(boundary) == 1 and boundary[0][1][0] != P.ONE:
                print("HIT", tuple(slot_names), "copy", boundary[0][0],
                      "terms", len(boundary[0][1][0]), flush=True)
                raise SystemExit(42)
print("tested", tested, "carrier_solutions", carriers, "hits 0")
