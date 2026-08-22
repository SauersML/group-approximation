#!/usr/bin/env python3
"""Exact bounded internal-solution search for the affine Omega word."""

import argparse
import importlib.util
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-composite-omega-internal-solutions.py")
SPEC = importlib.util.spec_from_file_location("internal", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def affine_word(t):
    # W_8=r t^2 a t^-1 c t^2 e t^-1 q t p t.
    tinv = P.inverse_word(t)
    return (("r",) + t + t + ("a",) + tinv + ("c",) + t + t
            + ("e",) + tinv + ("q",) + t + ("p",) + t)


parser = argparse.ArgumentParser()
parser.add_argument("--radius", type=int, default=4)
args = parser.parse_args()

tested = 0
solutions = []
for length in range(args.radius + 1):
    for candidate in P.reduced_words(length):
        tested += 1
        if P.evaluate(affine_word(candidate)) == P.ONE:
            solutions.append(candidate)
            print("SOLUTION", " ".join(candidate) or "1", flush=True)
    print("radius", length, "tested", tested, "solutions", len(solutions),
          flush=True)
print("DONE", "tested", tested, "solutions", len(solutions))
