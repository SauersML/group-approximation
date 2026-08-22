#!/usr/bin/env python3
"""Solve three Latin-triangle projections before testing the full boundary.

For target copy 0, E1=1 determines d=c a^-1 c b^-1 c.  Enumerate only
(a,b,c), check E2=E3=1 and E0=h, then verify the full free-product boundary.
"""

import argparse
import importlib.util
from itertools import product as cartesian
from pathlib import Path

SOURCE = Path(__file__).with_name("search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def invu(unit):
    return P.canon({(right, left) for left, right in unit})


def prod(*units):
    out = P.ONE
    for unit in units:
        out = P.mul(out, unit)
    return out


def reducew(word):
    stack = []
    for copy, unit in word:
        if unit == P.ONE:
            continue
        if stack and stack[-1][0] == copy:
            unit = P.mul(stack.pop()[1], unit)
            if unit == P.ONE:
                continue
        stack.append((copy, unit))
    return tuple(stack)


def invw(word):
    return tuple((copy, invu(unit)) for copy, unit in reversed(word))


u, v, h = prod(P.A, P.B), prod(P.C, P.D), P.TARGET
seeds = (("1", P.ONE), ("h", h), ("u", u), ("v", v),
         ("a", P.A), ("b", P.B), ("c", P.C), ("d", P.D),
         ("r", P.R), ("p", P.P), ("e", P.E))
atoms = {}
for name, unit in seeds:
    atoms.setdefault(unit, name)
    atoms.setdefault(invu(unit), name + "-")
atom_list = tuple(atoms.items())
library = dict(atoms)
for left, right in cartesian(atom_list, repeat=2):
    unit = P.mul(left[0], right[0])
    library.setdefault(unit, left[1] + "*" + right[1])
library = tuple((name, unit) for unit, name in library.items())

parser = argparse.ArgumentParser()
parser.add_argument("--a-index", type=int)
parser.add_argument("--size", action="store_true")
args = parser.parse_args()
if args.size:
    print(len(library))
    raise SystemExit
if args.a_index is None or not 0 <= args.a_index < len(library):
    parser.error("--a-index outside expanded library")

aname, a = library[args.a_index]
ai = invu(a)
tested = projection_survivors = 0
for bitem, citem in cartesian(library, repeat=2):
    bname, b = bitem
    cname, c = citem
    bi, ci = invu(b), invu(c)
    d = prod(c, ai, c, bi, c)  # E1=1 solved exactly
    di = invu(d)
    e2 = prod(di, c, di, b, di, a)
    e3 = prod(ai, d, ai, c, ai, b)
    tested += 1
    if e2 != P.ONE or e3 != P.ONE:
        continue
    e0 = prod(bi, a, bi, d, bi, c)
    if e0 != h:
        continue
    projection_survivors += 1
    H = reducew(((0, b), (1, c), (2, d), (3, a)))
    B0 = reducew(((0, a), (1, b), (2, c), (3, d)))
    B1 = reducew(((0, d), (1, a), (2, b), (3, c)))
    B2 = reducew(((0, c), (1, d), (2, a), (3, b)))
    F = reducew(invw(H) + B0 + invw(H) + B1 + invw(H) + B2)
    print("PROJECTION_SURVIVOR", "a_b_c", (aname, bname, cname),
          "derived_d", d, "F", F, flush=True)
    if F == ((0, h),):
        print("HIT", "a_b_c", (aname, bname, cname),
              "derived_d", d, "F", F, flush=True)
        raise SystemExit(42)

print("a_index", args.a_index, "a", aname, "tested", tested,
      "projection_survivors", projection_survivors, "hits 0")
