#!/usr/bin/env python3
"""Exact primal/dual certificates for finite transportation costs.

Input JSON:

  {
    "left":  {"a": "3/4", "b": "1/4"},
    "right": {"x": "1/4", "y": "3/4"},
    "costs": {"a|x": 0, "a|y": 1, "b|x": 1, "b|y": 0}
  }

The marginals are exact rationals and must have equal total mass.  Every pair
must have a cost.  The solver scales only the marginals to integers, then runs
successive shortest augmenting paths with exact Fraction costs.  A final
residual-graph potential produces a transportation-dual certificate

    x_i + y_j <= c_ij

whose objective equals the primal cost exactly.

This is deliberately stdlib-only and intended for the small fixed Fourier
alphabets appearing in the Cairn atlas routes.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from math import gcd
from pathlib import Path


def q(value):
    return Fraction(str(value))


def qstr(value):
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def lcm(a, b):
    return a // gcd(a, b) * b


def solve(data):
    left = {k: q(v) for k, v in data["left"].items()}
    right = {k: q(v) for k, v in data["right"].items()}
    if any(v < 0 for v in left.values()) or any(v < 0 for v in right.values()):
        raise ValueError("marginal weights must be nonnegative")
    if sum(left.values(), Fraction()) != sum(right.values(), Fraction()):
        raise ValueError("left and right marginal masses differ")

    L, R = sorted(left), sorted(right)
    costs = {}
    raw_costs = data["costs"]
    for i in L:
        for j in R:
            key = f"{i}|{j}"
            if key not in raw_costs:
                raise ValueError(f"missing cost {key!r}")
            costs[i, j] = q(raw_costs[key])

    den = 1
    for value in list(left.values()) + list(right.values()):
        den = lcm(den, value.denominator)
    supply = {i: int(left[i] * den) for i in L}
    demand = {j: int(right[j] * den) for j in R}
    total = sum(supply.values())

    source, sink = ("source",), ("sink",)
    lnode = {i: ("left", i) for i in L}
    rnode = {j: ("right", j) for j in R}
    nodes = [source] + [lnode[i] for i in L] + [rnode[j] for j in R] + [sink]

    capacity = defaultdict(int)
    flow = defaultdict(int)
    edge_cost = {}
    adj = defaultdict(set)

    def add_edge(u, v, cap, cost):
        capacity[u, v] += cap
        edge_cost[u, v] = cost
        edge_cost[v, u] = -cost
        adj[u].add(v)
        adj[v].add(u)

    for i in L:
        add_edge(source, lnode[i], supply[i], Fraction())
    for i in L:
        for j in R:
            add_edge(lnode[i], rnode[j], total, costs[i, j])
    for j in R:
        add_edge(rnode[j], sink, demand[j], Fraction())

    def shortest_path(start):
        """Bellman-Ford in the current residual graph; exact Fraction costs."""
        dist = {v: None for v in nodes}
        prev = {}
        dist[start] = Fraction()
        for _ in range(len(nodes) - 1):
            changed = False
            for u in nodes:
                if dist[u] is None:
                    continue
                for v in adj[u]:
                    if capacity[u, v] - flow[u, v] <= 0:
                        continue
                    cand = dist[u] + edge_cost[u, v]
                    if dist[v] is None or cand < dist[v]:
                        dist[v] = cand
                        prev[v] = u
                        changed = True
            if not changed:
                break
        return dist, prev

    sent = 0
    total_cost = Fraction()
    while sent < total:
        dist, prev = shortest_path(source)
        if dist[sink] is None:
            raise RuntimeError("transport network unexpectedly infeasible")
        amount = total - sent
        v = sink
        while v != source:
            u = prev[v]
            amount = min(amount, capacity[u, v] - flow[u, v])
            v = u
        v = sink
        while v != source:
            u = prev[v]
            flow[u, v] += amount
            flow[v, u] -= amount
            total_cost += amount * edge_cost[u, v]
            v = u
        sent += amount

    # At an optimal integral min-cost flow the residual graph has no negative
    # cycle.  Add a conceptual zero-cost super-source to every node by starting
    # all distances at zero; Bellman-Ford then returns a feasible reduced-cost
    # potential d with cost(u,v)+d(u)-d(v)>=0 on every residual arc.
    potential = {v: Fraction() for v in nodes}
    for step in range(len(nodes)):
        changed = False
        for u in nodes:
            for v in adj[u]:
                if capacity[u, v] - flow[u, v] <= 0:
                    continue
                cand = potential[u] + edge_cost[u, v]
                if cand < potential[v]:
                    potential[v] = cand
                    changed = True
        if not changed:
            break
    else:
        raise RuntimeError("negative residual cycle after min-cost flow")

    x = {i: -potential[lnode[i]] for i in L}
    y = {j: potential[rnode[j]] for j in R}
    primal_value = total_cost / den
    dual_value = (
        sum((left[i] * x[i] for i in L), Fraction())
        + sum((right[j] * y[j] for j in R), Fraction())
    )
    if primal_value != dual_value:
        raise RuntimeError(f"primal/dual mismatch: {primal_value} != {dual_value}")

    for i in L:
        for j in R:
            if x[i] + y[j] > costs[i, j]:
                raise RuntimeError(f"dual infeasible on {(i, j)!r}")

    plan = []
    for i in L:
        for j in R:
            amount = flow[lnode[i], rnode[j]]
            if amount > 0:
                plan.append({"left": i, "right": j, "mass": qstr(Fraction(amount, den))})

    return {
        "value": qstr(primal_value),
        "primal": plan,
        "dual_left": {i: qstr(x[i]) for i in L},
        "dual_right": {j: qstr(y[j]) for j in R},
        "weight_denominator": den,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    args = parser.parse_args()
    print(json.dumps(solve(json.loads(args.input.read_text())), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
