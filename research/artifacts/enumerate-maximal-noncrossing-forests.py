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


def maximal_forest_count(colors):
    colors = tuple(colors)

    @lru_cache(maxsize=None)
    def visit(left, right, forbidden):
        if left >= right:
            return 1
        color = colors[left]
        if forbidden & (1 << color):
            return 0
        peers = [index for index in range(left + 1, right)
                 if colors[index] == color]
        total = 0
        for width in range(len(peers) + 1):
            for tail in combinations(peers, width):
                previous, ways = left, 1
                for bound in tail:
                    ways *= visit(previous + 1, bound, 1 << color)
                    previous = bound
                    if not ways:
                        break
                if ways:
                    ways *= visit(previous + 1, right,
                                  forbidden | (1 << color))
                total += ways
        return total

    count = visit(0, len(colors), 0)
    return count, visit.cache_info().currsize


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("colors", help="comma-separated nonnegative colors")
    parser.add_argument("--show", type=int, default=0)
    parser.add_argument("--count-only", action="store_true")
    args = parser.parse_args()
    colors = tuple(map(int, args.colors.split(",")))
    if args.count_only:
        count, states = maximal_forest_count(colors)
        print(f"syllables={len(colors)}")
        print(f"maximal_forests={count}")
        print(f"cached_states={states}")
        return
    forests, states = maximal_forests(colors)
    print(f"syllables={len(colors)}")
    print(f"maximal_forests={len(forests)}")
    print(f"cached_states={states}")
    for forest in forests[:args.show]:
        print(forest)


if __name__ == "__main__":
    main()
