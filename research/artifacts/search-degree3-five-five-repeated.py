#!/usr/bin/env python3
"""Exact repeated-slot screen for all parameterized length-11 branches."""

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


def slots_for(mode, values):
    x0, x1, x2, x3, x4, x5 = values
    if mode in (0, 1):
        target = v if mode == 0 else inv_unit(v)
        g4, g5, g6, g7, g8, g9 = values
        g0 = inv_unit(target)
        g1 = prod(inv_unit(g4), inv_unit(g5))
        g2, g3 = inv_unit(g4), u
        g10 = prod(g0, g5, g4)
    elif mode == 2:
        g1, g5, g6, g7, g8, g9 = values
        g0, g2, g4 = h, P.ONE, P.ONE
        g3 = prod(inv_unit(g1), inv_unit(g5))
        g10 = prod(h, inv_unit(g1))
    else:
        g1, g5, g6, g7, g8, g9 = values
        g0, g3 = h, P.ONE
        g2 = prod(g1, g5)
        g4 = inv_unit(g2)
        g10 = prod(h, inv_unit(g1))
    return (g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10)


def replay(slots):
    hword = reduce_units(tuple((copy, slots[index]) for copy, index in
        ((0, 9), (1, 10), (2, 0), (1, 1), (0, 2), (1, 3),
         (0, 4), (1, 5), (2, 6), (1, 7), (2, 8))))
    hinv = inv_word(hword)
    left = reduce_units(((0, slots[6]),) + hword + ((2, slots[7]),) + hinv +
                        ((0, slots[8]), (1, slots[9]), (2, slots[10])))
    right = reduce_units(((0, slots[3]),) + hword + ((2, slots[4]),) + hinv +
                         ((0, slots[5]), (1, slots[6]), (0, slots[7]),
                          (1, slots[8]), (2, slots[9])))
    return left == right, hword, left


parser = argparse.ArgumentParser()
parser.add_argument("--mode", type=int, choices=range(4), required=True,
                    help="0/1: u-v/v^-1; 2/3: the two K=1 branches")
parser.add_argument("--shard", type=int, choices=range(len(LIBRARY)), required=True)
args = parser.parse_args()

fixed_name, fixed = LIBRARY[args.shard]
tested = 0
for tail in cartesian(LIBRARY, repeat=5):
    names = (fixed_name,) + tuple(item[0] for item in tail)
    values = (fixed,) + tuple(item[1] for item in tail)
    slots = slots_for(args.mode, values)
    equal, hword, boundary = replay(slots)
    tested += 1
    if equal:
        print("HIT", "mode", args.mode, "names", names,
              "slots", slots, "H", hword, "boundary", boundary, flush=True)
        raise SystemExit(42)

print("mode", args.mode, "shard", args.shard,
      "fixed", fixed_name, "tested", tested, "hits 0")
