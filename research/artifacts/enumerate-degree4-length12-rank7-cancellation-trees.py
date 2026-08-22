#!/usr/bin/env python3
"""Enumerate noncrossing cancellation schemes for the rank7 25-syllable word.

This is coefficient-group agnostic: a branch records the exact coefficient
equations whose satisfaction makes the free-product stack finish in copy 0.
"""

import argparse
from functools import lru_cache


def inverse_letter(letter):
    return letter.lower() if letter.isupper() else letter.upper()


@lru_cache(maxsize=None)
def normalize(word):
    # Free cancellation plus v^2=1 and [v,t]=1.  Canonicalize each maximal
    # {v,t,T} block as v^parity t^exponent, then repeat after cancellations.
    old = None
    word = tuple("v" if letter == "V" else letter for letter in word)
    while word != old:
        old = word
        out = []
        index = 0
        while index < len(word):
            if word[index] in ("v", "t", "T"):
                parity = exponent = 0
                while index < len(word) and word[index] in ("v", "t", "T"):
                    if word[index] == "v":
                        parity ^= 1
                    else:
                        exponent += 1 if word[index] == "t" else -1
                    index += 1
                if parity:
                    out.append("v")
                out.extend(("t",) * exponent if exponent >= 0 else ("T",) * -exponent)
                continue
            letter = word[index]
            if out and inverse_letter(out[-1]) == letter:
                out.pop()
            else:
                out.append(letter)
            index += 1
        word = tuple(out)
    return word


def multiply(left, right):
    return normalize(left + right)


def pretty(word):
    return "1" if not word else "".join(word)


SYLLABLES = (
    (3, "A"), (2, "tr"), (1, "vA"), (0, "vtra"),
    (1, "RTv"), (2, "av"), (3, "RA"), (2, "tr"),
    (1, "vA"), (0, "v"), (1, "a"), (2, "RTv"),
    (3, "avTA"), (2, "tr"), (1, "vA"),
    (0, "vtrSvARTv"), (1, "av"), (2, "RT"),
    (3, "avtr"), (2, "A"), (1, "tr"), (0, "sRTv"),
    (1, "av"), (2, "RT"), (3, "a"),
)
SYLLABLES = tuple((copy, normalize(tuple(word))) for copy, word in SYLLABLES)


parser = argparse.ArgumentParser()
parser.add_argument("--max-equations", type=int, default=10)
parser.add_argument("--examples", type=int, default=100)
args = parser.parse_args()

# State: (stack, frozenset equations).  Retain all equation sets through the
# requested depth; identical states are deduplicated exactly.
states = {((), frozenset())}
for position, (copy, coefficient) in enumerate(SYLLABLES):
    following = set()
    for stack, equations in states:
        # The incoming coefficient itself may be the identity.
        if len(equations) < args.max_equations:
            following.add((stack, equations | {coefficient}))
        # Or it survives.  If its copy meets the stack top, branch on whether
        # their exact product vanishes.
        if stack and stack[-1][0] == copy:
            combined = multiply(stack[-1][1], coefficient)
            if combined:
                following.add((stack[:-1] + ((copy, combined),), equations))
                if len(equations) < args.max_equations:
                    following.add((stack[:-1], equations | {combined}))
            else:
                following.add((stack[:-1], equations))
        else:
            following.add((stack + ((copy, coefficient),), equations))
    states = following
    print("position", position + 1, "states", len(states), flush=True)

solutions = []
for stack, equations in states:
    if len(stack) == 1 and stack[0][0] == 0 and stack[0][1]:
        solutions.append((len(equations), stack[0][1], equations))
solutions.sort(key=lambda item: (item[0], pretty(item[1]),
                                 tuple(sorted(map(pretty, item[2])))))
print("solutions", len(solutions))
for count, target, equations in solutions[:args.examples]:
    print("SCHEME", count, "target", pretty(target), "equations",
          tuple(sorted(pretty(equation) for equation in equations)))
