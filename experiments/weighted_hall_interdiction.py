#!/usr/bin/env python3
"""Exact target synthesis for weighted Hall edge interdiction.

Given a baseline bipartite graph, rational vertex weights, and nonnegative
rational deletion costs, find a minimum-cost edge set whose deletion creates a
strict weighted Hall deficit. This is the constructive backend for
`weighted-hall-interdiction-formula`.

The solver is exact. It scales all vertex weights to integers, enumerates
subsets on the smaller side, and solves the other side by 0-1 knapsack dynamic
programming. It is intended for finite Fourier/type quotient graphs, not for
hundreds of ungrouped matrix-index vertices.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd
from pathlib import Path


def as_fraction(x):
    return Fraction(str(x))


def frac(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def lcm(a, b):
    return a // gcd(a, b) * b


def scale_weights(left, right):
    den = 1
    for value in list(left.values()) + list(right.values()):
        den = lcm(den, value.denominator)
    return (
        den,
        {k: int(v * den) for k, v in left.items()},
        {k: int(v * den) for k, v in right.items()},
    )


def edge_key(i, j):
    return f"{i}|{j}"


def solve(data):
    left = {k: as_fraction(v) for k, v in data["left"].items()}
    right = {k: as_fraction(v) for k, v in data["right"].items()}
    allowed = {tuple(e) for e in data["allowed"]}
    for i, j in allowed:
        if i not in left or j not in right:
            raise ValueError(f"unknown allowed edge {(i, j)!r}")

    raw_costs = data.get("edge_costs")
    costs = {}
    for e in allowed:
        i, j = e
        value = 1 if raw_costs is None else raw_costs.get(edge_key(i, j), 1)
        costs[e] = as_fraction(value)
        if costs[e] < 0:
            raise ValueError("edge deletion costs must be nonnegative")

    den, a, b = scale_weights(left, right)
    L, R = sorted(left), sorted(right)
    best = None

    def consider(cost, S, T):
        nonlocal best
        A = sum(a[i] for i in S)
        B = sum(b[j] for j in T)
        if A <= B:
            return
        deletion = sorted([[i, j] for i, j in allowed if i in S and j not in T])
        deficit = Fraction(A - B, den)
        candidate = {
            "cost": cost,
            "deficit": deficit,
            "source_subset": list(S),
            "target_cap": list(T),
            "delete": deletion,
        }
        key = (cost, -deficit, len(deletion), tuple(S), tuple(T))
        if best is None or key < best[0]:
            best = (key, candidate)

    # For fixed S, choose T by a max-saved-cost knapsack under beta(T)<alpha(S).
    if len(L) <= len(R):
        for mask in range(1, 1 << len(L)):
            S = tuple(L[k] for k in range(len(L)) if (mask >> k) & 1)
            A = sum(a[i] for i in S)
            if A <= 0:
                continue
            delete_if_excluded = {
                j: sum((costs.get((i, j), Fraction()) for i in S), Fraction())
                for j in R
            }
            base = sum(delete_if_excluded.values(), Fraction())
            cap = A - 1  # strict inequality after exact integer scaling
            dp = {0: (Fraction(), ())}
            for j in R:
                w, value = b[j], delete_if_excluded[j]
                nxt = dict(dp)
                for weight, (saved, chosen) in dp.items():
                    new_weight = weight + w
                    if new_weight <= cap:
                        cand = (saved + value, chosen + (j,))
                        old = nxt.get(new_weight)
                        if old is None or (cand[0], cand[1]) > (old[0], old[1]):
                            nxt[new_weight] = cand
                dp = nxt
            _, (saved, T) = max(
                dp.items(), key=lambda item: (item[1][0], item[0], item[1][1])
            )
            consider(base - saved, S, T)
    else:
        # For fixed T, choose S by a min-cost knapsack cover alpha(S)>beta(T).
        for mask in range(1 << len(R)):
            T = tuple(R[k] for k in range(len(R)) if (mask >> k) & 1)
            B = sum(b[j] for j in T)
            required = B + 1
            delete_if_selected = {
                i: sum(
                    (costs.get((i, j), Fraction()) for j in R if j not in T),
                    Fraction(),
                )
                for i in L
            }
            dp = {0: (Fraction(), ())}
            for i in L:
                w, value = a[i], delete_if_selected[i]
                nxt = dict(dp)
                for weight, (cost, chosen) in dp.items():
                    new_weight = min(required, weight + w)
                    cand = (cost + value, chosen + (i,))
                    old = nxt.get(new_weight)
                    if old is None or (cand[0], cand[1]) < (old[0], old[1]):
                        nxt[new_weight] = cand
                dp = nxt
            if required in dp:
                cost, S = dp[required]
                consider(cost, S, T)

    if best is None:
        return {"found": False}
    out = best[1]
    return {
        "found": True,
        "minimum_deletion_cost": frac(out["cost"]),
        "hall_deficit": frac(out["deficit"]),
        "source_subset": out["source_subset"],
        "target_cap": out["target_cap"],
        "delete": out["delete"],
        "weight_denominator": den,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    print(json.dumps(solve(data), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
