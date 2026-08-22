#!/usr/bin/env python3
"""Enumerate only maximal noncrossing schemes for inverse I1;412 Eq3."""

from functools import lru_cache
from itertools import combinations, product


COLORS = (3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 1,
          2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 1, 2, 3)


@lru_cache(maxsize=None)
def maximal(lo, hi):
    if lo == hi:
        return (0, ((),))
    candidates = [i for i in range(lo + 1, hi)
                  if COLORS[i] == COLORS[lo]]
    best = hi - lo + 1
    winners = set()
    for width in range(len(candidates) + 1):
        for tail in combinations(candidates, width):
            block = (lo,) + tail
            bounds = block + (hi,)
            pieces = [maximal(left + 1, right)
                      for left, right in zip(bounds, bounds[1:])]
            score = 1 + sum(piece[0] for piece in pieces)
            if score > best:
                continue
            if score < best:
                best, winners = score, set()
            for choices in product(*(piece[1] for piece in pieces)):
                winners.add(tuple(sorted((block,) + sum(choices, ()))))
    return best, tuple(sorted(winners))


def main():
    count, schemes = maximal(0, len(COLORS))
    print(f"minimum_blocks={count}")
    print(f"maximal_schemes={len(schemes)}")
    for scheme in schemes:
        print(scheme)


if __name__ == "__main__":
    main()

