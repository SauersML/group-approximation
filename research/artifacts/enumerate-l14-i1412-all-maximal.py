#!/usr/bin/env python3
"""Enumerate every coarsening-maximal colored NC partition for I1;412.

Starting from the singleton partition, every allowed edge merges two
same-colored blocks whose union remains noncrossing.  Leaves are therefore
exactly the partitions maximal under coarsening, including locally maximal
partitions with more than the global minimum number of blocks.
"""

import argparse
import importlib.util
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


EQ3 = load("i1412_eq3", "enumerate-l14-i1412-eq3-maximal.py")
EQ1 = load("i1412_eq1", "enumerate-l14-i1412-eq1-maximal.py")


def enumerate_leaves(colors):
    @lru_cache(maxsize=None)
    def forests(lo, hi, parent_color):
        """Maximal forests, paired with their distinct top-level colors."""
        if lo == hi:
            return (((), ()),)
        root_color = colors[lo]
        if root_color == parent_color:
            return ()
        candidates = [index for index in range(lo + 1, hi)
                      if colors[index] == root_color]
        answers = set()
        for width in range(len(candidates) + 1):
            for tail in combinations(candidates, width):
                block = (lo,) + tail
                internal_bounds = block + (block[-1] + 1,)
                gaps = tuple((left + 1, right)
                             for left, right in zip(internal_bounds,
                                                    internal_bounds[1:])
                             if left + 1 < right)
                child_options = [forests(left, right, root_color)
                                 for left, right in gaps]
                if any(not options for options in child_options):
                    continue
                suffix_options = forests(block[-1] + 1, hi, parent_color)
                for children in product(*child_options) if child_options else ((),):
                    child_partition = sum((entry[0] for entry in children), ())
                    for suffix_partition, suffix_colors in suffix_options:
                        if root_color in suffix_colors:
                            continue
                        partition = tuple(sorted(
                            (block,) + child_partition + suffix_partition,
                            key=lambda item: item[0]))
                        answers.add((partition, (root_color,) + suffix_colors))
        return tuple(sorted(answers))

    entries = forests(0, len(colors), -1)
    leaves = {partition for partition, _ in entries}
    return forests.cache_info().currsize, leaves


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("equation", choices=("eq1", "eq3"))
    args = parser.parse_args()
    module = EQ1 if args.equation == "eq1" else EQ3
    cached_intervals, leaves = enumerate_leaves(module.COLORS)
    histogram = {}
    for leaf in leaves:
        histogram[len(leaf)] = histogram.get(len(leaf), 0) + 1
    print(f"equation={args.equation}")
    print(f"cached_forest_states={cached_intervals}")
    print(f"coarsening_maximal_partitions={len(leaves)}")
    print(f"block_histogram={dict(sorted(histogram.items()))}")


if __name__ == "__main__":
    main()
