#!/usr/bin/env python3
"""Find a maximum weighted Hall deficit by exact rational max-flow/min-cut.

This is the finite combinatorial backend for
`atlas-wedderburn-hall-deficient-support-certificate`.  Input is a bipartite
allowed-edge graph with rational source/target weights.  The output is an
exact deficient source set and its neighbor set when one exists.

Example input::

    {
      "left": {"a": "2/3", "b": "1/3"},
      "right": {"x": "1/3", "y": "2/3"},
      "allowed": [["a", "x"], ["b", "x"], ["b", "y"]]
    }

The implementation is standard-library-only and uses `Fraction` throughout.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from fractions import Fraction
from pathlib import Path


def as_fraction(value):
    return Fraction(str(value))


def fraction_string(value):
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())

    left = {name: as_fraction(weight)
            for name, weight in data["left"].items()}
    right = {name: as_fraction(weight)
             for name, weight in data["right"].items()}
    allowed = [tuple(edge) for edge in data["allowed"]]

    source, sink = ("source",), ("sink",)
    capacity = {}
    adjacency = {}

    def add_edge(u, v, cap):
        capacity[(u, v)] = capacity.get((u, v), Fraction()) + cap
        capacity.setdefault((v, u), Fraction())
        adjacency.setdefault(u, set()).add(v)
        adjacency.setdefault(v, set()).add(u)

    total_left = sum(left.values(), Fraction())
    infinity = total_left + sum(right.values(), Fraction()) + 1

    for name, weight in left.items():
        add_edge(source, ("L", name), weight)
    for name, weight in right.items():
        add_edge(("R", name), sink, weight)
    for l_name, r_name in allowed:
        if l_name not in left or r_name not in right:
            raise SystemExit(f"unknown allowed edge {l_name!r}, {r_name!r}")
        add_edge(("L", l_name), ("R", r_name), infinity)

    flow = {edge: Fraction() for edge in capacity}
    value = Fraction()

    # Edmonds--Karp is more than sufficient for the fixed finite Fourier graphs
    # this tool is meant to audit, and exact rationals keep the certificate
    # independent of numerical tolerances.
    while True:
        parent = {source: None}
        queue = deque([source])
        while queue and sink not in parent:
            u = queue.popleft()
            for v in sorted(adjacency.get(u, ()), key=str):
                if v in parent:
                    continue
                if capacity[(u, v)] - flow[(u, v)] > 0:
                    parent[v] = u
                    queue.append(v)
        if sink not in parent:
            break

        bottleneck = None
        v = sink
        while parent[v] is not None:
            u = parent[v]
            residual = capacity[(u, v)] - flow[(u, v)]
            bottleneck = residual if bottleneck is None else min(
                bottleneck, residual)
            v = u

        v = sink
        while parent[v] is not None:
            u = parent[v]
            flow[(u, v)] += bottleneck
            flow[(v, u)] -= bottleneck
            v = u
        value += bottleneck

    reachable = {source}
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in adjacency.get(u, ()):
            if v in reachable:
                continue
            if capacity[(u, v)] - flow[(u, v)] > 0:
                reachable.add(v)
                queue.append(v)

    source_subset = sorted(
        name for name in left if ("L", name) in reachable)
    neighbor_subset = sorted(
        name for name in right if ("R", name) in reachable)

    deficit = (
        sum((left[name] for name in source_subset), Fraction())
        - sum((right[name] for name in neighbor_subset), Fraction())
    )
    if deficit != total_left - value:
        raise AssertionError("min-cut / Hall-deficit replay failed")

    print(json.dumps({
        "total_source_weight": fraction_string(total_left),
        "max_flow": fraction_string(value),
        "hall_deficit": fraction_string(deficit),
        "deficient": deficit > 0,
        "source_subset": source_subset,
        "neighbor_subset": neighbor_subset,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
