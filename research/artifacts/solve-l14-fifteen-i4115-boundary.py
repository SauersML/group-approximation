#!/usr/bin/env python3
"""Run the exact cyclic boundary solver for fifteen-winner I(4;115)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = spec_from_file_location(name, HERE / filename)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BOUNDARY = load("fifteen_n0115_boundary",
                "solve-l14-fifteen-n0115-boundary.py")
STATES = load("fifteen_i4115_states",
              "solve-l14-fifteen-i4115-maximal-states.py")
BOUNDARY.S = STATES
BOUNDARY.Q = 6
BOUNDARY.IDENTITY = tuple((index,) for index in range(1, 7))
BOUNDARY.combine.cache_clear()
BOUNDARY.relation_state.cache_clear()
BOUNDARY.maximal_states.cache_clear()


if __name__ == "__main__":
    BOUNDARY.main()
