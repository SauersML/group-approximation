#!/usr/bin/env python3
"""Compile exact carriers/boundary for fifteen-winner inverse class I(1;115)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


COMPILER = Path(__file__).with_name("compile-l14-fifteen-n0115.py")
SPEC = spec_from_file_location("compile_l14_fifteen_n0115", COMPILER)
RAW = module_from_spec(SPEC)
SPEC.loader.exec_module(RAW)

multiply = RAW.multiply
inverse = RAW.inverse
H = RAW.H

# Actual atom start 2 represents cyclic key 1;115:
# T2=id0, T3 T4 T5 T6 T0=id5^-1, T1=id4.
R0 = multiply(inverse(H), RAW.B0, H, RAW.E3)
R2 = multiply(inverse(H), RAW.C0, H, RAW.A1)
R4 = multiply(inverse(H), RAW.B1, inverse(H), RAW.E2)
K = multiply(inverse(RAW.A0), inverse(H), inverse(RAW.C1), H,
             inverse(RAW.E1), inverse(H), inverse(RAW.E7), H,
             inverse(RAW.E6), inverse(H), inverse(RAW.E5), H,
             inverse(RAW.E4), H)


def main():
    for name, word in (("R0", R0), ("R2", R2), ("R4", R4), ("K", K)):
        RAW.show(name, word)
        RAW.show_projections(name, word)


if __name__ == "__main__":
    main()
