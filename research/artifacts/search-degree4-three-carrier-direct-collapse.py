#!/usr/bin/env python3
"""Exact direct-collapse screen for the degree-4 length-10 (1,3,3,3) cover.

After solving the unary orbit, require two of the three residual relators to
be coefficient identities and the remaining relator to be exactly h in one
coefficient copy.  Slots repeat over a small structural library.  Copy
retractions are checked before full free-product normal form.
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


def mul_word(left, right):
    return reduce_units(left + right)


def power_word(word, exponent):
    if exponent < 0:
        word, exponent = inv_word(word), -exponent
    out = ()
    for _ in range(exponent):
        out = mul_word(out, word)
    return out


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def orbit_corners(slots, signs, start):
    height = start
    raw = []
    for unit, sign in zip(slots, signs):
        residue = height % 4
        quotient = (height - residue) // 4
        append_z(raw, quotient)
        raw.append(("g", residue, unit))
        append_z(raw, -quotient)
        height += sign
    append_z(raw, 1)
    expanded = []
    for token in raw:
        if token[0] == "z":
            step = 1 if token[1] > 0 else -1
            expanded.extend(("z", step) for _ in range(abs(token[1])))
        else:
            expanded.append(token)
    first = next(index for index, token in enumerate(expanded)
                 if token[0] == "z")
    expanded = expanded[first:] + expanded[:first]
    corners = []
    index = 0
    while index < len(expanded):
        sign = expanded[index][1]
        index += 1
        corner = []
        while index < len(expanded) and expanded[index][0] != "z":
            _, copy, unit = expanded[index]
            corner.append((copy, unit))
            index += 1
        corners.append((sign, reduce_units(tuple(corner))))
    return tuple(corners)


def evaluate(corners, pivot):
    out = ()
    for sign, corner in corners:
        out = mul_word(out, power_word(pivot, -sign))
        out = mul_word(out, corner)
    return out


def project(word, copy):
    out = P.ONE
    for index, unit in word:
        if index == copy:
            out = P.mul(out, unit)
    return out


def prod(*units):
    out = P.ONE
    for unit in units:
        out = P.mul(out, unit)
    return out


u = prod(P.A, P.B)
v = prod(P.C, P.D)
h = P.TARGET
LIBRARY = (("1", P.ONE), ("h", h), ("u", u),
           ("v", v), ("v-", inv_unit(v)))
SIGNS = (-1, -1, -1, 1, 1, 1, 1, 1, 1, 1)


parser = argparse.ArgumentParser()
parser.add_argument("--shard", type=int, choices=range(25), required=True,
                    help="fix the first two of ten coefficient slots")
args = parser.parse_args()
fixed = (LIBRARY[args.shard // 5], LIBRARY[args.shard % 5])

tested = projection_survivors = 0
for tail in cartesian(LIBRARY, repeat=8):
    assignment = fixed + tail
    names = tuple(item[0] for item in assignment)
    slots = tuple(item[1] for item in assignment)
    orbits = tuple(orbit_corners(slots, SIGNS, start) for start in range(4))
    assert tuple(map(len, orbits)) == (3, 3, 3, 1)
    pivot = orbits[3][0][1]
    residuals = tuple(evaluate(orbits[index], pivot) for index in range(3))
    tested += 1
    for target in range(3):
        if any(residuals[index] for index in range(3) if index != target):
            continue
        for copy in range(4):
            if all(project(residuals[target], index) ==
                   (h if index == copy else P.ONE) for index in range(4)):
                projection_survivors += 1
                if residuals[target] == ((copy, h),):
                    print("HIT", "target_orbit", target, "target_copy", copy,
                          "slot_names", names, "pivot", pivot,
                          "residuals", residuals, flush=True)
                    raise SystemExit(42)

print("shard", args.shard, "fixed", tuple(item[0] for item in fixed),
      "tested", tested, "projection_survivors", projection_survivors,
      "hits 0")
