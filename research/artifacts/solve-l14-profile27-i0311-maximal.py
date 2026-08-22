#!/usr/bin/env python3
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

PATH = Path(__file__).with_name("solve-l14-profile27-131-maximal-base.py")
SPEC = spec_from_file_location("profile27_i0311_solver_base", PATH)
B = module_from_spec(SPEC)
SPEC.loader.exec_module(B)
S = B.install("compress-l14-profile27-i0311.py", "i0311")
# The shared solver names its two live inputs r2/r4; install R0,R4 here.
S.WORDS = {"r2": S.C.R0, "r4": S.C.R4, "boundary": S.C.K}
C, P, ALG, encode = S.C, S.P, S.ALG, S.encode
combine, maximal_states, WORDS = S.combine, S.maximal_states, S.WORDS

if __name__ == "__main__":
    S.main()
