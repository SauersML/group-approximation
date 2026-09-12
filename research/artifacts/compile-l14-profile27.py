#!/usr/bin/env python3
"""Compile the three rank-nine classes for profile ---+++--++++++."""

import argparse
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


BASE = Path(__file__).with_name("compile-l14-profile18.py")
SPEC = spec_from_file_location("compile_l14_profile18_base", BASE)
B = module_from_spec(SPEC)
SPEC.loader.exec_module(B)

PROFILE = tuple(1 if sign == "+" else -1 for sign in "---+++--++++++")
RAW = tuple(B.raw_corners(PROFILE, start) for start in range(4))
PIVOT = next(face for face in RAW if len(face) == 1)
B.H = PIVOT[0][1]
B.FACES = tuple(sorted((face for face in RAW if len(face) != 1), key=len))

B.SELECTIONS = {
    "N0131": (
        (((0,), (0, 1)), ((1,), (1, 1)), ((2,), (2, 1))),
        (((0,), (2, -1)), ((1, 2, 3), (3, 1)), ((4,), (4, 1))),
        (((0,), (4, -1)), ((1, 2, 3), (5, 1)), ((4,), (0, -1))),
    ),
    "I0131": (
        (((0,), (2, -1)), ((1,), (1, -1)), ((2,), (0, -1))),
        (((0,), (4, -1)), ((1, 2, 3), (3, -1)), ((4,), (2, 1))),
        (((0,), (0, 1)), ((1, 2, 3), (5, -1)), ((4,), (4, 1))),
    ),
    "I0311": (
        (((0,), (2, -1)), ((1,), (1, -1)), ((2,), (0, -1))),
        (((0, 1, 2), (4, -1)), ((3,), (3, -1)), ((4,), (2, 1))),
        (((0, 1, 2), (0, 1)), ((3,), (5, -1)), ((4,), (4, 1))),
    ),
}

compile_selection = B.compile_selection
project = B.project


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("class_name", choices=tuple(B.SELECTIONS))
    args = parser.parse_args()
    print(f"class={args.class_name}")
    print(f"H_syllables={len(B.H)}")
    for name, word in compile_selection(B.SELECTIONS[args.class_name]).items():
        B.show(name, word)


if __name__ == "__main__":
    main()
