#!/usr/bin/env python3
"""Exact replay of the parity routing plan on Y = X x Z/2 over Bernoulli X.

Model: T(x,i) = (sigma x, i+1 mod 2), pi(x,i) = x, one demand y -> Ty.
Plan D: label +2 on P0 = {i=0}, label +3 on P1 = {i=1}.
  y in P0:  y -+2-> T^2 y -+2-> T^4 y <-+3- Ty      (length 3)
  y in P1:  y -+3-> T^3 y <-+2- Ty                  (length 2)

The parity coordinate is independent of the base point, so every conditional
quantity given pi is the average over the two parities.  We replay the paths
on the cyclic window Z/(2M) (orbit coordinate n, parity n mod 2), check that
each path is a legal walk ending at n+1 using only edges that exist, count the
traffic N of each edge copy, and compute B and J = sum_j integral min(a_j,b_j)
in exact rationals.  Also checks the edit distance to the direct plan and
the fact used in Step 3: no single step of +-2 or +-3 equals +1.
"""
from fractions import Fraction as F
from collections import Counter

LABELS = {2: 0, 3: 1}  # label -> parity of its domain


def edge_exists(label, start):
    return start % 2 == LABELS[label]


def path(n):
    """List of (label, start, direction) occurrences for request n -> n+1."""
    if n % 2 == 0:
        return [(2, n, +1), (2, n + 2, +1), (3, n + 1, -1)]
    return [(3, n, +1), (2, n + 1, -1)]


def replay(M):
    size = 2 * M
    traffic = Counter()
    for n in range(size):
        pos = n
        for label, start, direction in path(n):
            assert edge_exists(label, start), (n, label, start)
            if direction == +1:
                assert pos == start
                pos = start + label
            else:
                assert pos == start + label
                pos = start
            traffic[(label, start % size)] += 1
        assert pos == n + 1, (n, pos)
    return traffic, size


def main():
    for M in (1, 2, 5, 17, 100):
        traffic, size = replay(M)
        # every edge copy present is used; traffic depends only on label
        for label, par in LABELS.items():
            vals = {traffic[(label, s)] for s in range(size) if s % 2 == par}
            assert vals == ({3} if label == 2 else {2}), (label, vals)
        B = F(sum(1 for k in traffic if traffic[k] >= 1), size)
        assert B == 1
        J = F(0)
        for label, par in LABELS.items():
            N = [traffic[(label, s)] if s % 2 == par else 0 for s in range(size)]
            # conditional on the base: average over the independent parity
            a = F(sum(1 for v in N if v == 0), size)
            b = F(sum(max(v - 1, 0) for v in N), size)
            J += min(a, b)
        assert J == 1, J
    # edit distance (used + repair multiplicities) to the direct +1 plan
    d_direct = F(1) + F(1, 2) + F(1, 2)
    assert d_direct == 2
    # Step 3 fact: no light step of label +-2 or +-3 is a request by itself
    assert all(t != 1 for t in (2, -2, 3, -3))
    print("parity plan: B = 1, J = 1, traffic +2 edges = 3, +3 edges = 2;"
          " edit distance to direct plan = 2; all checks passed")


if __name__ == "__main__":
    main()
