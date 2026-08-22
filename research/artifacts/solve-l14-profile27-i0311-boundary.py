#!/usr/bin/env python3
"""Run the audited cyclic boundary solver for profile27 I(0;311)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


PATH = Path(__file__).with_name("solve-l14-profile27-131-boundary-base.py")
SPEC = spec_from_file_location("profile27_i0311_boundary_base", PATH)
B = module_from_spec(SPEC)
SPEC.loader.exec_module(B)
W = B.install("solve-l14-profile27-i0311-maximal.py", "i0311")


if __name__ == "__main__":
    W.main()
