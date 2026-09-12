#!/usr/bin/env python3
"""Reuse the audited all-maximal solver for the normal 131 core."""

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = load("profile18_n0131_compression", "compress-l14-profile18-n0131.py")
S = load("profile18_i0131_solver", "solve-l14-profile18-i0131-maximal.py")
S.C = C
S.NUMBER = {name: index + 1 for index, name in enumerate(C.FREE)}
S.IDENTITY = tuple((index,) for index in range(1, len(C.FREE) + 1))
S.combine.cache_clear()
S.relation_state.cache_clear()
S.EMPTY = S.P.close_tietze((), S.IDENTITY)
S.WORDS = {"r2": C.R2, "r4": C.R4, "boundary": C.K}

# Re-export the state machinery for the boundary wrapper.
P, ALG, encode = S.P, S.ALG, S.encode
combine, maximal_states, WORDS = S.combine, S.maximal_states, S.WORDS


if __name__ == "__main__":
    S.main()
