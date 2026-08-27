#!/usr/bin/env python3
"""Compile exact carriers/boundary for fifteen-winner class N(0;214)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


COMPILER = Path(__file__).with_name("compile-l14-fifteen-n0115.py")
SPEC = spec_from_file_location("compile_l14_fifteen_n0115", COMPILER)
RAW = module_from_spec(SPEC)
SPEC.loader.exec_module(RAW)

multiply = RAW.multiply
inverse = RAW.inverse
H = RAW.H

# Ranker representative:
# atoms T3..T6=id4^-1, atoms T0 T1=id5, atom T2=id0^-1.
R0 = multiply(H, RAW.A0, H, RAW.E3)
R2 = multiply(inverse(H), RAW.C0, H, RAW.A1)
R4 = multiply(inverse(H), RAW.C1, inverse(H), RAW.E4,
              inverse(H), RAW.E5, H, RAW.E6, inverse(H), RAW.E7)
K = multiply(inverse(H), RAW.B0, inverse(H), RAW.B1,
             H, RAW.E1, inverse(H), RAW.E2)


def main():
    for name, word in (("R0", R0), ("R2", R2), ("R4", R4), ("K", K)):
        RAW.show(name, word)
        RAW.show_projections(name, word)


if __name__ == "__main__":
    main()
