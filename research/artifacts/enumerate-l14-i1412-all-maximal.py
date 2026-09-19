#!/usr/bin/env python3
"""Count every coarsening-maximal NC partition for an I1;412 carrier."""

import argparse
import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


EQ3 = load("i1412_eq3", "enumerate-l14-i1412-eq3-maximal.py")
EQ1 = load("i1412_eq1", "enumerate-l14-i1412-eq1-maximal.py")
FORESTS = load("maximal_nc_forests", "enumerate-maximal-noncrossing-forests.py")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("equation", choices=("eq1", "eq3"))
    args = parser.parse_args()
    module = EQ1 if args.equation == "eq1" else EQ3
    leaves, cached_intervals = FORESTS.maximal_forests(module.COLORS)
    histogram = {}
    for leaf in leaves:
        histogram[len(leaf)] = histogram.get(len(leaf), 0) + 1
    print(f"equation={args.equation}")
    print(f"cached_forest_states={cached_intervals}")
    print(f"coarsening_maximal_partitions={len(leaves)}")
    print(f"block_histogram={dict(sorted(histogram.items()))}")


if __name__ == "__main__":
    main()
