#!/usr/bin/env python3
"""Compile exact carriers/boundary for fifteen-winner inverse class I(4;115)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


COMPILER = Path(__file__).with_name("compile-l14-fifteen-n0115.py")
SPEC = spec_from_file_location("compile_l14_fifteen_n0115", COMPILER)
RAW = module_from_spec(SPEC)
SPEC.loader.exec_module(RAW)

multiply = RAW.multiply
inverse = RAW.inverse
H = RAW.H

# Actual atom start 5 represents cyclic key 4;115:
# T5=id0, T6 T0 T1 T2 T3=id5^-1, T4=id4.
R0 = multiply(inverse(H), RAW.B0, H, RAW.E6)
R2 = multiply(inverse(H), RAW.C0, H, RAW.A1)
R4 = multiply(inverse(H), RAW.B1, inverse(H), RAW.E5)
K = multiply(inverse(RAW.A0), inverse(H), inverse(RAW.C1), H,
             inverse(RAW.E4), H, inverse(RAW.E3), inverse(H),
             inverse(RAW.E2), H, inverse(RAW.E1), inverse(H),
             inverse(RAW.E7), H)


def main():
    for name, word in (("R0", R0), ("R2", R2), ("R4", R4), ("K", K)):
        RAW.show(name, word)
        RAW.show_projections(name, word)


if __name__ == "__main__":
    main()
