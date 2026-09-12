#!/usr/bin/env python3
"""Color-only noncrossing DP for the three-winner H!=1 boundary.

The exact boundary is K=H^-1 B0 H^-1 B1 H^-1 E4 after g0=g3=1.
This first-stage filter counts the least constrained cancellation topologies;
coefficient equations are replayed only for those topologies in the next
stage.
"""

from functools import lru_cache
from itertools import combinations


COLORS = (
    3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 1, 2, 3, 2, 3,
    2, 1, 2, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 3, 2,
    1, 2, 1, 2, 1, 2, 1, 0, 1, 2, 3,
)


@lru_cache(maxsize=None)
def optimum(left, right):
    """Return (minimum blocks, number of minimizing partitions)."""
    if left >= right:
        return 0, 1
    candidates = [index for index in range(left + 1, right)
                  if COLORS[index] == COLORS[left]]
    best, count = right - left + 1, 0
    for width in range(len(candidates) + 1):
        for tail in combinations(candidates, width):
            block = (left,) + tail
            bounds = block + (right,)
            blocks, ways = 1, 1
            previous = left
            for bound in bounds[1:]:
                local_blocks, local_ways = optimum(previous + 1, bound)
                blocks += local_blocks
                ways *= local_ways
                previous = bound
            if blocks < best:
                best, count = blocks, ways
            elif blocks == best:
                count += ways
    return best, count


def main():
    blocks, ways = optimum(0, len(COLORS))
    print(f"syllables={len(COLORS)}")
    print("color_word=" + ",".join(map(str, COLORS)))
    print(f"minimum_noncrossing_blocks={blocks}")
    print(f"minimizing_partitions={ways}")
    print(f"cached_intervals={optimum.cache_info().currsize}")


if __name__ == "__main__":
    main()
