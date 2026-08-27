#!/usr/bin/env python3
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

PATH = Path(__file__).with_name("solve-l14-profile27-131-boundary-base.py")
SPEC = spec_from_file_location("profile27_131_boundary_base_n", PATH)
B = module_from_spec(SPEC)
SPEC.loader.exec_module(B)
W = B.install("solve-l14-profile27-n0131-maximal.py", "n0131")

if __name__ == "__main__":
    W.main()
