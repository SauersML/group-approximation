#!/usr/bin/env python3
"""Apply the exact copy-projection retraction to class I(0;131)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


COMPILER = Path(__file__).with_name("compile-l14-profile18.py")
SPEC = spec_from_file_location("compile_l14_profile18", COMPILER)
RAW = module_from_spec(SPEC)
SPEC.loader.exec_module(RAW)

TIETZE_PATH = Path(__file__).with_name("enumerate-l14-i1412-carrier-pairs.py")
TIETZE_SPEC = spec_from_file_location("i1412_pairs_for_profile18", TIETZE_PATH)
TIETZE = module_from_spec(TIETZE_SPEC)
TIETZE_SPEC.loader.exec_module(TIETZE)

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


# a,...,h are g4,...,g11.  These are the literal Tietze images returned by
# the ten nonempty copy projections of R0,R2,R4.
SUBSTITUTION = {
    "g0": (),
    "g1": (("d", -1), ("b", -1)),
    "g2": (("c", -1), ("a", -1)),
    "g3": (),
    "g4": (("a", 1),),
    "g5": (("b", 1),),
    "g6": (("c", 1),),
    "g7": (("d", 1),),
    "g8": (("e", 1),),
    "g9": (("f", 1),),
    "g10": (("g", 1),),
    "g11": (("h", 1),),
    "g12": (("b", -1), ("a", 1), ("c", 1)),
    "g13": (("b", 1), ("d", 1)),
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


SYSTEM = RAW.compile_selection(RAW.SELECTIONS["I0131"])


def encode_raw(coefficient):
    return tuple(sign * (int(name[1:]) + 1) for name, sign in coefficient)


RAW_PROJECTIONS = tuple(
    encode_raw(RAW.project(SYSTEM[name], copy))
    for name in ("R0", "R2", "R4") for copy in range(4)
    if RAW.project(SYSTEM[name], copy)
)
EXPECTED_IMAGES = tuple(
    tuple(sign * (FREE.index(name) + 5) for name, sign in SUBSTITUTION[f"g{slot}"])
    for slot in range(14)
)
assert TIETZE.close_tietze(RAW_PROJECTIONS,
                           tuple((index,) for index in range(1, 15))) == (
                               (), EXPECTED_IMAGES)

R0 = substitute_word(SYSTEM["R0"])
R2 = substitute_word(SYSTEM["R2"])
R4 = substitute_word(SYSTEM["R4"])
K = substitute_word(SYSTEM["K"])

# Replay the projection elimination, including the vanished first carrier.
assert R0 == ()
for relation in (R2, R4):
    assert all(project(relation, copy) == () for copy in range(4))


def show(name, word):
    print(f"{name}_syllables={len(word)}")
    print(f"{name}_colors=" + ",".join(str(copy) for copy, _ in word))
    for index, (copy, coefficient) in enumerate(word):
        text = " ".join(generator + ("^-1" if sign < 0 else "")
                        for generator, sign in coefficient)
        print(f"{name}[{index}]={copy}:{text}")


def main():
    for name, word in (("R0", R0), ("R2", R2), ("R4", R4), ("K", K)):
        show(name, word)


if __name__ == "__main__":
    main()
