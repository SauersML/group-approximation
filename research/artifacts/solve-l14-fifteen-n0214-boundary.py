#!/usr/bin/env python3
"""Run the exact cyclic boundary solver for fifteen-winner N(0;214)."""

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
STATES = load("fifteen_n0214_states",
              "solve-l14-fifteen-n0214-maximal-states.py")

# The reusable solver carries one fresh q-coordinate after the five compressed
# coefficient coordinates of this class.
BOUNDARY.S = STATES
BOUNDARY.Q = 6
BOUNDARY.IDENTITY = tuple((index,) for index in range(1, 7))
BOUNDARY.combine.cache_clear()
BOUNDARY.relation_state.cache_clear()
BOUNDARY.maximal_states.cache_clear()


if __name__ == "__main__":
    BOUNDARY.main()
