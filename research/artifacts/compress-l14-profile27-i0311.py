#!/usr/bin/env python3
"""Exact free-rank-eight core of profile27 I(0;311)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = spec_from_file_location(name, HERE / filename)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


RAW = load("compile_l14_profile27_i0311", "compile-l14-profile27.py")
TIETZE = load("i1412_pairs_profile27_i0311",
              "enumerate-l14-i1412-carrier-pairs.py")
FREE = ("a", "b", "c", "d", "e", "f", "g", "h")


def inverse_coefficient(word):
    return tuple((name, -sign) for name, sign in reversed(word))


def reduce_coefficient(word):
    out = []
    for letter in word:
        if out and out[-1] == (letter[0], -letter[1]):
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


# a,...,h are original coordinate generators 5,7,8,9,10,11,12,13.
SUBSTITUTION = {
    "g0": (),
    "g1": (("e", -1), ("h", 1), ("d", -1), ("a", -1)),
    "g2": (("d", -1), ("a", -1)),
    "g3": (), "g4": (("a", 1),),
    "g5": (("a", 1), ("d", 1), ("h", -1), ("c", -1)),
    "g6": (("b", 1),), "g7": (("c", 1),),
    "g8": (("d", 1),), "g9": (("e", 1),),
    "g10": (("f", 1),), "g11": (("g", 1),),
    "g12": (("h", 1),),
    "g13": (("b", -1), ("a", 1), ("d", 1), ("h", -1),
             ("e", 1)),
}


def substitute_coefficient(word):
    out = ()
    for name, sign in word:
        image = SUBSTITUTION[name]
        if sign < 0:
            image = inverse_coefficient(image)
        out = reduce_coefficient(out + image)
    return out


def substitute_word(word):
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


SYSTEM = RAW.compile_selection(RAW.B.SELECTIONS["I0311"])
RAW_PROJECTIONS = tuple(
    tuple(sign * (int(name[1:]) + 1) for name, sign in
          RAW.project(SYSTEM[relation], copy))
    for relation in ("R0", "R2", "R4") for copy in range(4)
    if RAW.project(SYSTEM[relation], copy)
)
EXPECTED_IMAGES = tuple(
    tuple(sign * ((5, 7, 8, 9, 10, 11, 12, 13)[FREE.index(name)])
          for name, sign in SUBSTITUTION[f"g{slot}"])
    for slot in range(14)
)
assert TIETZE.close_tietze(
    RAW_PROJECTIONS, tuple((index,) for index in range(1, 15))) == (
        (), EXPECTED_IMAGES)
WORDS = {name: substitute_word(word) for name, word in SYSTEM.items()}
R0, R2, R4, K = (WORDS[name] for name in ("R0", "R2", "R4", "K"))
assert R2 == ()
assert (len(R0), len(R4), len(K)) == (41, 41, 41)
