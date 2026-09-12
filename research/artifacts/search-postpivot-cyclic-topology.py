#!/usr/bin/env python3
"""Find cyclic sign words realizing a unary orbit and a valence-nine gate.

This is a topology-only Reidemeister--Schreier screen.  Coefficient slots are
kept as their original indices, so a later exact solver can assign Leavitt
coefficients without repeating the sign enumeration.
"""

import argparse
from itertools import combinations


def append_z(word, exponent):
    if word and word[-1][0] == "z":
        exponent += word.pop()[1]
    if exponent:
        word.append(("z", exponent))


def orbit_word(signs, start, degree):
    height = start
    word = []
    for slot, sign in enumerate(signs):
        residue = height % degree
        quotient = (height - residue) // degree
        append_z(word, quotient)
        word.append(("g", residue, slot))
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


def signed_corners(word):
    first = next(i for i, token in enumerate(word) if token[0] == "z")
    word = word[first:] + word[:first]
    out = []
    i = 0
    while i < len(word):
        sign = word[i][1]
        i += 1
        corner = []
        while i < len(word) and word[i][0] != "z":
            corner.append((word[i][1], word[i][2]))
            i += 1
        out.append((sign, tuple(corner)))
    return tuple(out)


parser = argparse.ArgumentParser()
parser.add_argument("--max-length", type=int, default=18)
args = parser.parse_args()

hits = 0
for length in range(9, args.max_length + 1):
    for degree in range(1, min(8, length) + 1):
        if (length - degree) % 2:
            continue
        negative_count = (length - degree) // 2
        for negative in combinations(range(length), negative_count):
            signs = tuple(-1 if i in negative else 1 for i in range(length))
            orbits = tuple(signed_corners(orbit_word(signs, start, degree))
                           for start in range(degree))
            unary = [i for i, orbit in enumerate(orbits) if len(orbit) == 1]
            targets = [i for i, orbit in enumerate(orbits)
                       if len(orbit) == 9]
            if not unary or not targets:
                continue
            for target in targets:
                target_signs = tuple(sign for sign, _ in orbits[target])
                # Necessary for a post-pivot D-valued relator: the target
                # incidence has sign sum one and one X=z^-1 corner.
                if sum(target_signs) != 1:
                    continue
                hits += 1
                print("HIT", "length", length, "degree", degree,
                      "signs", signs, "unary", unary, "target", target,
                      "unary_signed_corners",
                      tuple(orbits[index] for index in unary),
                      "target_signed_corners", orbits[target], flush=True)
                if hits >= 100:
                    raise SystemExit
print("hits", hits)
