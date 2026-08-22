#!/usr/bin/env python3
"""Exact all-maximal carrier states for fifteen-winner inverse I(4;115)."""

import argparse
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = spec_from_file_location(name, HERE / filename)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = load("fifteen_n0115_states",
            "solve-l14-fifteen-n0115-maximal-states.py")
C = load("fifteen_i4115_compression",
         "compress-l14-fifteen-i4115-projections.py")
P, ALG = BASE.P, BASE.ALG


def solver(branch):
    free = (("s", "t", "u", "w", "c") if branch == "I" else
            ("s", "t", "u", "v", "c"))
    return BASE.build_solver(C, branch, free, ("c",))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("branch", choices=("I", "II"))
    parser.add_argument("equation", choices=("r0", "r4", "both", "boundary"))
    args = parser.parse_args()
    maximal, words, combine, _, _ = solver(args.branch)
    if args.equation == "both":
        left, left_intervals = maximal(words["r0"])
        right, right_intervals = maximal(words["r4"])
        states = tuple(sorted({combine(a, b) for a in left for b in right}))
        print(f"branch={args.branch}")
        print(f"r0_states={len(left)}")
        print(f"r4_states={len(right)}")
        print(f"cached_intervals={left_intervals + right_intervals}")
        print(f"combined_coordinate_states={len(states)}")
    else:
        states, intervals = maximal(words[args.equation])
        print(f"branch={args.branch}")
        print(f"equation={args.equation}")
        print(f"syllables={len(words[args.equation])}")
        print(f"cached_intervals={intervals}")
        print(f"coordinate_tietze_states={len(states)}")
    print(f"abstract_presentations={len(set(r for r, _ in states))}")
    for state in states[:100]:
        print(state)


if __name__ == "__main__":
    main()
