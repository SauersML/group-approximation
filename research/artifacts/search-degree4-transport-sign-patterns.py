#!/usr/bin/env python3
"""Search degree-four sign/slot layouts for an exact source-target transport.

A successful layout has one unary pivot corner X and two trivalent orbit
relators.  The latter have singleton corners a,b in one coefficient copy and
c,d in another, while both remaining corners are exactly X.  Then the unary
relation cancels the final z in both trivalent relations and conjugates the
commuting source pair to the noncommuting target pair.
"""

import importlib.util
from itertools import combinations, permutations
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("degree4_pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

NAMES = ("r", "e", "a", "c", "1", "b", "d", "p")
UNITS = {
    "r": P.R, "e": P.E, "a": P.A, "c": P.C,
    "b": P.B, "d": P.D, "p": P.P,
}


def append_z(word, exponent):
    if not exponent:
        return
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def orbit_word(slots, signs, start):
    height = start
    word = []
    for name, sign in zip(slots, signs):
        residue = height % 4
        quotient = (height - residue) // 4
        append_z(word, quotient)
        if name != "1":
            word.append(("g", residue, name))
        append_z(word, -quotient)
        height += sign
    append_z(word, 1)
    expanded = []
    for token in word:
        if token[0] == "z":
            step = 1 if token[1] > 0 else -1
            expanded.extend(("z", step) for _ in range(abs(token[1])))
        else:
            expanded.append(token)
    return tuple(expanded)


def corners(word):
    first = next(i for i, token in enumerate(word) if token[0] == "z")
    word = word[first:] + word[:first]
    out = []
    i = 0
    while i < len(word):
        assert word[i][0] == "z"
        i += 1
        corner = []
        while i < len(word) and word[i][0] != "z":
            corner.append((word[i][1], word[i][2]))
            i += 1
        out.append(tuple(corner))
    return tuple(out)


def reduce_corner(corner):
    stack = []
    for copy, name in corner:
        unit = UNITS[name]
        if stack and stack[-1][0] == copy:
            unit = P.mul(stack.pop()[1], unit)
            if unit == P.ONE:
                continue
        stack.append((copy, unit))
    return tuple(stack)


def singleton(corner):
    if len(corner) == 1 and corner[0][1] in ("a", "b", "c", "d"):
        return corner[0]
    return None


tested = 0
structural = 0
hits = []
for negative_positions in combinations(range(8), 2):
    signs = tuple(-1 if i in negative_positions else 1 for i in range(8))
    for slots in permutations(NAMES):
        tested += 1
        orbit_corners = tuple(corners(orbit_word(slots, signs, start))
                              for start in range(4))
        unary = [(i, cs[0], reduce_corner(cs[0]))
                 for i, cs in enumerate(orbit_corners) if len(cs) == 1]
        trivalent = [(i, cs) for i, cs in enumerate(orbit_corners)
                     if len(cs) == 3]
        if not unary or len(trivalent) < 2:
            continue
        unary_values = {value for _, _, value in unary if value}
        for first_index in range(len(trivalent)):
            for second_index in range(first_index + 1, len(trivalent)):
                selected = (trivalent[first_index], trivalent[second_index])
                tails = []
                gates = []
                valid = True
                for _, cs in selected:
                    matching = [j for j, corner in enumerate(cs)
                                if reduce_corner(corner) in unary_values]
                    if len(matching) != 1:
                        valid = False
                        break
                    tail = matching[0]
                    tails.append(cs[tail])
                    other = [singleton(corner) for j, corner in enumerate(cs)
                             if j != tail]
                    if any(value is None for value in other):
                        valid = False
                        break
                    gates.extend(other)
                if not valid:
                    continue
                structural += 1
                by_name = {name: copy for copy, name in gates}
                if set(by_name) != {"a", "b", "c", "d"}:
                    continue
                if by_name["a"] != by_name["b"]:
                    continue
                if by_name["c"] != by_name["d"]:
                    continue
                hit = (negative_positions, slots,
                       tuple(index for index, _, _ in unary),
                       tuple(index for index, _ in selected),
                       tuple(tails), tuple(gates))
                hits.append(hit)
                print("HIT", hit, flush=True)

print("tested", tested)
print("structural_tail_collisions", structural)
print("transport_hits", len(hits))
