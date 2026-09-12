#!/usr/bin/env python3
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

PATH = Path(__file__).with_name("solve-l14-profile27-131-maximal-base.py")
SPEC = spec_from_file_location("profile27_131_solver_base_n", PATH)
B = module_from_spec(SPEC)
SPEC.loader.exec_module(B)
S = B.install("compress-l14-profile27-n0131.py", "n0131")
C, P, ALG, encode = S.C, S.P, S.ALG, S.encode
combine, maximal_states, WORDS = S.combine, S.maximal_states, S.WORDS
