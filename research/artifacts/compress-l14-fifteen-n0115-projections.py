#!/usr/bin/env python3
"""Substitute copy retractions and the two exact R2 branches for N(0;115)."""

import argparse

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


COMPILER = Path(__file__).with_name("compile-l14-fifteen-n0115.py")
SPEC = spec_from_file_location("compile_l14_fifteen_n0115", COMPILER)
RAW = module_from_spec(SPEC)
SPEC.loader.exec_module(RAW)


def inverse_coefficient(word):
    return tuple((name, -sign) for name, sign in reversed(word))


INVOLUTIONS = frozenset(("A", "B", "C", "E"))


def normalize_letter(name, sign):
    return name, 1 if name in INVOLUTIONS else sign


def reduce_coefficient(word):
    out = []
    for name, sign in word:
        letter = normalize_letter(name, sign)
        if out and out[-1] == (letter[0], -letter[1]):
            out.pop()
        elif out and letter[0] in INVOLUTIONS and out[-1] == letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


# Free parameters q=g9,r=g10,s=g13,t=g1,u=g2 and involutions
# A=g9g11, B=g10g12, C=g13g1g7, E=g8.
SUBSTITUTION = {
    "g0": (),
    "g1": (("t", 1),),
    "g2": (("u", 1),),
    "g3": (("E", 1), ("C", -1), ("s", 1), ("E", 1)),
    "g4": (("A", 1), ("t", -1), ("s", -1), ("A", 1)),
    "g5": (("E", 1), ("s", -1), ("C", 1), ("E", 1)),
    "g6": (("A", 1), ("s", 1), ("t", 1), ("A", 1), ("u", -1)),
    "g7": (("t", -1), ("s", -1), ("C", 1)),
    "g8": (("E", 1),),
    "g9": (("q", 1),),
    "g10": (("r", 1),),
    "g11": (("q", -1), ("A", 1)),
    "g12": (("r", -1), ("B", 1)),
    "g13": (("s", 1),),
}


def substitute_coefficient(word):
    out = ()
    for name, sign in word:
        image = SUBSTITUTION[name]
        if sign < 0:
            image = inverse_coefficient(image)
        out = reduce_coefficient(out + image)
    return out


def multiply(word):
    out = []
    for copy, coefficient in word:
        coefficient = substitute_coefficient(coefficient)
        if not coefficient:
            continue
        if out and out[-1][0] == copy:
            coefficient = reduce_coefficient(out[-1][1] + coefficient)
            out.pop()
            if coefficient:
                out.append((copy, coefficient))
        else:
            out.append((copy, coefficient))
    return tuple(out)


def project(word, target):
    out = ()
    for copy, coefficient in word:
        if copy == target:
            out = reduce_coefficient(out + coefficient)
    return out


def branch_reduce_coefficient(word, branch):
    branch_involutions = INVOLUTIONS | ({"s"} if branch == "I" else set())
    out = []
    for name, sign in word:
        if branch == "I" and name == "C":
            name, sign = "s", 1
        elif branch == "II" and name == "t":
            name, sign = "s", -sign
        if name in branch_involutions:
            sign = 1
        letter = name, sign
        if out and out[-1] == (name, -sign):
            out.pop()
        elif name in branch_involutions and out and out[-1] == letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def branch_reduce(word, branch):
    out = []
    for copy, coefficient in word:
        coefficient = branch_reduce_coefficient(coefficient, branch)
        if not coefficient:
            continue
        if out and out[-1][0] == copy:
            coefficient = branch_reduce_coefficient(out[-1][1] + coefficient,
                                                    branch)
            out.pop()
            if coefficient:
                out.append((copy, coefficient))
        else:
            out.append((copy, coefficient))
    return tuple(out)


def show(name, word, assert_trivial_projections=False):
    print(f"{name}_syllables={len(word)}")
    print(f"{name}_colors=" + ",".join(str(copy) for copy, _ in word))
    for index, (copy, coefficient) in enumerate(word):
        text = " ".join(generator + ("^-1" if sign < 0 else "")
                        for generator, sign in coefficient)
        print(f"{name}[{index}]={copy}:{text}")
    if assert_trivial_projections:
        for target in range(4):
            assert project(word, target) == (), (name, target,
                                                  project(word, target))


R0 = multiply(RAW.R0)
R2 = multiply(RAW.R2)
R4 = multiply(RAW.R4)
K = multiply(RAW.K)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", choices=("I", "II"))
    args = parser.parse_args()
    # Replay definitions of the four involutions and every eliminated slot.
    assert reduce_coefficient(SUBSTITUTION["g9"] + SUBSTITUTION["g11"]
                              + (("A", 1),)) == ()
    assert reduce_coefficient(SUBSTITUTION["g10"] + SUBSTITUTION["g12"]
                              + (("B", 1),)) == ()
    assert reduce_coefficient(SUBSTITUTION["g13"] + SUBSTITUTION["g1"]
                              + SUBSTITUTION["g7"] + (("C", 1),)) == ()
    assert SUBSTITUTION["g8"] == (("E", 1),)
    words = (("R0", R0), ("R2", R2), ("R4", R4), ("K", K))
    if args.branch:
        words = tuple((name, branch_reduce(word, args.branch))
                      for name, word in words)
        assert words[1][1] == (), (args.branch, words[1][1])
    for name, word in words[:3]:
        show(name, word, assert_trivial_projections=not args.branch)
    show("K", words[3][1])


if __name__ == "__main__":
    main()
