#!/usr/bin/env python3
"""Enumerate all coarsening-maximal monochromatic NC partitions exactly."""

import argparse
from functools import lru_cache
from itertools import combinations


def maximal_forests(colors):
    colors = tuple(colors)

    @lru_cache(maxsize=None)
    def visit(left, right, forbidden):
        if left >= right:
            return ((),)
        color = colors[left]
        if forbidden & (1 << color):
            return ()
        peers = [index for index in range(left + 1, right)
                 if colors[index] == color]
        out = set()
        for width in range(len(peers) + 1):
            for tail in combinations(peers, width):
                block = (left,) + tail
                previous, products = left, [()]
                valid = True
                for bound in tail:
                    choices = visit(previous + 1, bound, 1 << color)
                    if not choices:
                        valid = False
                        break
                    products = [prefix + choice for prefix in products
                                for choice in choices]
                    previous = bound
                if not valid:
                    continue
                suffixes = visit(previous + 1, right,
                                 forbidden | (1 << color))
                for prefix in products:
                    for suffix in suffixes:
                        out.add(tuple(sorted((block,) + prefix + suffix)))
        return tuple(sorted(out))

    result = visit(0, len(colors), 0)
    return result, visit.cache_info().currsize


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("colors", help="comma-separated nonnegative colors")
    parser.add_argument("--show", type=int, default=0)
    args = parser.parse_args()
    colors = tuple(map(int, args.colors.split(",")))
    forests, states = maximal_forests(colors)
    print(f"syllables={len(colors)}")
    print(f"maximal_forests={len(forests)}")
    print(f"cached_states={states}")
    for forest in forests[:args.show]:
        print(forest)


if __name__ == "__main__":
    main()
