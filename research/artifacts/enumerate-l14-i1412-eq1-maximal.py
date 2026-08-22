#!/usr/bin/env python3
"""Enumerate maximal noncrossing schemes for inverse I1;412 Eq1.

This imports the audited free-product/Tietze machinery from the Eq3 screen and
retains a raw-name assertion for the independently expanded 31 syllables.
"""

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "i1412_eq3", HERE / "enumerate-l14-i1412-eq3-maximal.py")
EQ3 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EQ3)

COLORS = (3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 1, 2, 3, 2, 1, 2,
          1, 2, 1, 2, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2, 3)
RAW_S = (
    (("g10", -1),), (("g9", -1),), (("g8", -1),), (("g7", -1),),
    (("g6", -1),), (("g5", -1),), (("g4", -1), ("g2", -1)),
    (("g1", -1), ("g13", -1)), (("g12", -1),),
    (("g11", -1), ("g10", 1)), (("g11", 1),), (("g12", 1),),
    (("g13", 1), ("g10", -1)), (("g9", -1),), (("g8", -1),),
    (("g7", -1),), (("g6", -1),), (("g5", -1),),
    (("g4", -1), ("g2", -1)), (("g1", -1), ("g13", -1)),
    (("g12", -1),),
    (("g11", -1), ("g13", 1), ("g1", 1), ("g11", 1)),
    (("g12", 1),), (("g13", 1), ("g1", 1)),
    (("g2", 1), ("g4", 1)), (("g5", 1),), (("g6", 1),),
    (("g7", 1),), (("g8", 1),), (("g9", 1),),
    (("g10", 1), ("g2", 1), ("g4", 1)),
)
S = tuple(tuple(sign * EQ3.NUMBER[name] for name, sign in syllable)
          for syllable in RAW_S)
assert len(S) == len(COLORS) == 31


def main():
    EQ3.COLORS = COLORS
    EQ3.maximal.cache_clear()
    count, schemes = EQ3.maximal(0, len(COLORS))
    print(f"minimum_blocks={count}")
    print(f"maximal_schemes={len(schemes)}")
    presentations = set()
    for scheme in schemes:
        relations = [EQ3.reduce_word(sum((S[index] for index in block), ()))
                     for block in scheme]
        presentations.add(EQ3.tietze(relations))
    print(f"tietze_presentations={len(presentations)}")
    for presentation in sorted(presentations)[:100]:
        print(presentation)


if __name__ == "__main__":
    main()
