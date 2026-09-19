#!/usr/bin/env python3
"""Shared exact projection retraction for profile27 N/I(0;131)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = spec_from_file_location(name, HERE / filename)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


RAW = load("compile_l14_profile27", "compile-l14-profile27.py")
TIETZE = load("i1412_pairs_for_profile27", "enumerate-l14-i1412-carrier-pairs.py")
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


SUBSTITUTION = {
    "g0": (), "g1": (("b", -1),), "g2": (("a", -1),), "g3": (),
    "g4": (("a", 1),), "g5": (("b", 1),),
    "g6": (("c", 1),), "g7": (("d", 1),),
    "g8": (("e", 1),), "g9": (("f", 1),),
    "g10": (("g", 1),), "g11": (("h", 1),),
    "g12": (("a", 1),), "g13": (("b", 1),),
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


def project(word, target):
    out = ()
    for copy, coefficient in word:
        if copy == target:
            out = reduce_coefficient(out + coefficient)
    return out


def build(class_name):
    system = RAW.compile_selection(RAW.B.SELECTIONS[class_name])
    raw_projections = tuple(
        tuple(sign * (int(name[1:]) + 1) for name, sign in
              RAW.project(system[relation], copy))
        for relation in ("R0", "R2", "R4") for copy in range(4)
        if RAW.project(system[relation], copy)
    )
    expected_images = tuple(
        tuple(sign * (FREE.index(name) + 5)
              for name, sign in SUBSTITUTION[f"g{slot}"])
        for slot in range(14)
    )
    assert TIETZE.close_tietze(
        raw_projections, tuple((index,) for index in range(1, 15))) == (
            (), expected_images)
    words = {name: substitute_word(word) for name, word in system.items()}
    assert words["R0"] == words["R2"] == words["R4"] == ()
    assert all(substitute_coefficient(RAW.project(system[relation], copy)) == ()
               for relation in ("R0", "R2", "R4") for copy in range(4))
    return system, words
