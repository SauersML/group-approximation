#!/usr/bin/env python3
"""Apply the exact projection collapse to class N(0;131)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = spec_from_file_location(name, HERE / filename)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


RAW = load("compile_l14_profile18", "compile-l14-profile18.py")
TIETZE = load("i1412_pairs_for_profile18_n",
              "enumerate-l14-i1412-carrier-pairs.py")
ALG = TIETZE.EQ3
FREE = ("a", "b", "c", "d", "e")


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


# a,b,c,d,e are g1,g2,g4,g5,g11.  The two composite roots in the projection
# presentation are forced trivial by the certificate below.
SUBSTITUTION = {
    "g0": (), "g1": (("a", 1),), "g2": (("b", 1),), "g3": (),
    "g4": (("c", 1),), "g5": (("d", 1),),
    "g6": (("c", -1), ("b", -1)),
    "g7": (("d", -1), ("a", -1), ("b", 1), ("c", 1)),
    "g8": (("a", -1), ("b", 1), ("c", 1)),
    "g9": (("a", -1), ("b", 1), ("c", 1), ("e", -1)),
    "g10": (("a", -1), ("b", 1), ("c", 1), ("b", 1), ("d", 1)),
    "g11": (("e", 1),),
    "g12": (("d", -1), ("b", -1)),
    "g13": (("a", -1),),
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


SYSTEM = RAW.compile_selection(RAW.SELECTIONS["N0131"])


def encode_raw(coefficient):
    return tuple(sign * (int(name[1:]) + 1) for name, sign in coefficient)


RAW_PROJECTIONS = tuple(
    encode_raw(RAW.project(SYSTEM[name], copy))
    for name in ("R0", "R2", "R4") for copy in range(4)
    if RAW.project(SYSTEM[name], copy)
)
PROJECTION_STATE = TIETZE.close_tietze(
    RAW_PROJECTIONS, tuple((index,) for index in range(1, 15)))
assert PROJECTION_STATE[0] == (
    (-8, -6, -2, 3, 5) * 3,
    (-7, -5, -3, -8, -6, -2, 3, 5, -8, -6, -2, 3, 5,
     -7, -5, -3, -8, -6, -2, 3, 5, -8, -6, -2, 3, 5,
     -8, -6, -2, 3, 5, 3, 5, 7),
    (-5, -3, 2, 6, 8) * 6 + (-7, -5, -3)
    + (-5, -3, 2, 6, 8) * 2 + (-7, -5, -3)
    + (-8, -6, -2, 3, 5) * 2,
)

# Introduce p=15=(-8,-6,-2,3,5) and B=16=(-7,-5,-3), eliminating
# generators 8 and 7 respectively.  Literal substitution gives this pair
# presentation.
PAIR_RELATIONS = tuple(ALG.substitute(ALG.substitute(relation, 8,
    (-6, -2, 3, 5, -15)), 7, (-5, -3, -16))
    for relation in PROJECTION_STATE[0])
assert PAIR_RELATIONS == (
    (15, 15, 15),
    (16, 15, 15, 16, 15, 15, 15, -16),
    (-15, -15, -15, -15, -15, -15, 16, -15, -15, 16, 15, 15),
)
# p^3=1 reduces the second relation to Bp^2, hence B=p.  Substitution in
# the third reduces it to p^2; gcd(2,3)=1, so p=B=1.  The final images below
# are also checked directly against every original projection.
assert ALG.reduce_word(ALG.substitute(PAIR_RELATIONS[2], 16, (15,))) == \
    (-15, -15, -15, -15)

R0 = substitute_word(SYSTEM["R0"])
R2 = substitute_word(SYSTEM["R2"])
R4 = substitute_word(SYSTEM["R4"])
K = substitute_word(SYSTEM["K"])
assert all(substitute_coefficient(RAW.project(SYSTEM[name], copy)) == ()
           for name in ("R0", "R2", "R4") for copy in range(4))
assert R0 == ()
for relation in (R2, R4):
    assert all(project(relation, copy) == () for copy in range(4))


def main():
    for name, word in (("R0", R0), ("R2", R2), ("R4", R4), ("K", K)):
        print(f"{name}_syllables={len(word)}")
        print(f"{name}_colors=" + ",".join(str(copy) for copy, _ in word))


if __name__ == "__main__":
    main()
