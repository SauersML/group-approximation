#!/usr/bin/env python3
"""Exact repeated-slot screen for the length-13 (1,5,7) K=1 branches.

The source five-corner word is trivial in each of the four exhaustive
free-product cancellation branches.  The target three-syllable corner is h.
Unlike the earlier packet screens, coefficient slots may repeat and may be 1.
"""

import argparse
import importlib.util
from itertools import product as cartesian
from pathlib import Path


SOURCE = Path(__file__).with_name("search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def inv_unit(unit):
    return P.canon({(right, left) for left, right in unit})


def inv_word(word):
    return tuple((copy, inv_unit(unit)) for copy, unit in reversed(word))


def reduce_units(factors):
    stack = []
    for copy, unit in factors:
        if unit == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            unit = P.mul(stack.pop()[1], unit)
            if unit == P.ONE:
                continue
        stack.append((copy, unit))
    return tuple(stack)


def prod(*units):
    out = P.ONE
    for unit in units:
        out = P.mul(out, unit)
    return out


u = prod(P.A, P.B)
v = prod(P.C, P.D)
h = P.TARGET
LIBRARY = (
    ("1", P.ONE), ("h", h), ("u", u), ("v", v),
    ("v-", inv_unit(v)), ("a", P.A), ("b", P.B),
    ("c", P.C), ("d", P.D), ("r", P.R), ("p", P.P), ("e", P.E),
)


def slots_for(branch, values):
    g1, x, y, g8, g9, g10, g11 = values
    if branch == 1:
        g3, g5 = x, y
        g2 = g4 = g6 = P.ONE
        g7 = inv_unit(prod(g1, g3, g5))
    elif branch == 2:
        g5, g7 = x, y
        g2 = prod(g1, g5, g7)
        g3 = g6 = P.ONE
        g4 = inv_unit(g2)
    elif branch == 3:
        g3, g4 = x, y
        g2 = g5 = P.ONE
        g6 = inv_unit(g4)
        g7 = inv_unit(prod(g1, g3))
    else:
        g4, g6 = x, y
        g2 = inv_unit(prod(g4, g6))
        g3 = g5 = P.ONE
        g7 = prod(inv_unit(g1), g2)
    g0 = h
    g12 = prod(h, inv_unit(g1))
    return (g0, g1, g2, g3, g4, g5, g6,
            g7, g8, g9, g10, g11, g12)


def replay(slots):
    hword = reduce_units(tuple((copy, slots[index]) for copy, index in
        ((0, 11), (1, 12), (2, 0), (1, 1), (0, 2), (1, 3),
         (0, 4), (1, 5), (0, 6), (1, 7), (2, 8), (1, 9), (2, 10))))
    hinv = inv_word(hword)
    left = reduce_units(((0, slots[8]),) + hword + ((2, slots[9]),) + hinv +
                        ((0, slots[10]), (1, slots[11]), (2, slots[12])))
    right = reduce_units(((0, slots[3]),) + hword + ((2, slots[4]),) + hinv +
                         ((0, slots[5]),) + hword + ((2, slots[6]),) + hinv +
                         ((0, slots[7]), (1, slots[8]), (0, slots[9]),
                          (1, slots[10]), (2, slots[11])))
    return left == right, hword, left


parser = argparse.ArgumentParser()
parser.add_argument("--branch", type=int, choices=range(1, 5), required=True)
parser.add_argument("--shard", type=int, choices=range(len(LIBRARY)), required=True,
                    help="fix the first free parameter g1")
args = parser.parse_args()

fixed_name, fixed = LIBRARY[args.shard]
tested = 0
for tail in cartesian(LIBRARY, repeat=6):
    names = (fixed_name,) + tuple(item[0] for item in tail)
    values = (fixed,) + tuple(item[1] for item in tail)
    slots = slots_for(args.branch, values)
    equal, hword, boundary = replay(slots)
    tested += 1
    if equal:
        print("HIT", "branch", args.branch, "names", names,
              "slots", slots, "H", hword, "boundary", boundary, flush=True)
        raise SystemExit(42)

print("branch", args.branch, "shard", args.shard,
      "fixed_g1", fixed_name, "tested", tested, "hits 0")
