#!/usr/bin/env python3
"""Run the audited Q-first cyclic boundary solver for N(0;131)."""

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


S = load("profile18_n0131_states", "solve-l14-profile18-n0131-maximal.py")
W = load("profile18_i0131_boundary", "solve-l14-profile18-i0131-boundary.py")
W.S = S
W.B.S = S
W.B.C = S.C
W.B.ALG = S.ALG
W.B.Q = len(S.C.FREE) + 1
W.B.IDENTITY = tuple((index,) for index in range(1, W.B.Q + 1))
W.B.combine.cache_clear()
W.B.relation_state.cache_clear()
W.B.maximal_states_relative.cache_clear()
W.B.ENCODED_K = tuple((copy, S.encode(coefficient))
                      for copy, coefficient in S.C.K)


if __name__ == "__main__":
    W.main()
