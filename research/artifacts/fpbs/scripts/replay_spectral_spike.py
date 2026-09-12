#!/usr/bin/env python3
"""Exact finite checks for spectral-spike.md, using only the standard library.

This checks finite identities. It does not prove the infinite probabilistic,
representation-theoretic, or universal-conjecture statements in the note.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def partitions(n: int):
    """Restricted-growth words encode every partition of n labeled vertices."""
    if n < 1:
        raise ValueError("n must be positive")
    def extend(word: tuple[int, ...]):
        if len(word) == n:
            yield word
            return
        for x in range(max(word) + 2):
            yield from extend(word + (x,))
    yield from extend((0,))


def partition_sign_checks() -> dict:
    cases = checks = assignments = 0
    for n in range(1, 6):
        for word in partitions(n):
            k = max(word) + 1
            for marked_mask in range(1 << k):
                # Marked blocks are abstract stand-ins for infinite classes.
                finite = [b for b in range(k) if not ((marked_mask >> b) & 1)]
                covariance = [[0 for _ in range(n)] for _ in range(n)]
                count = 1 << len(finite)
                for signs in product((-1, 1), repeat=len(finite)):
                    values = dict(zip(finite, signs))
                    v = [values.get(b, 0) for b in word]
                    assignments += 1
                    for i in range(n):
                        for j in range(n):
                            covariance[i][j] += v[i] * v[j]
                for i in range(n):
                    for j in range(n):
                        cov = F(covariance[i][j], count)
                        marked_i = bool((marked_mask >> word[i]) & 1)
                        marked_j = bool((marked_mask >> word[j]) & 1)
                        same = word[i] == word[j]
                        assert cov == int(same and not marked_i)
                        assert cov + int(marked_i and marked_j) == (
                            int(same) + int(marked_i and marked_j and not same)
                        )
                        checks += 2
                cases += 1
    return {"partition_marking_cases": cases,
            "enumerated_sign_assignments": assignments,
            "exact_identity_assertions": checks}


GRAPHS = {
    "path4": (4, [(0, 1), (1, 2), (2, 3)]),
    "cycle3": (3, [(0, 1), (1, 2), (0, 2)]),
    "cycle4": (4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
    "cycle5": (5, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]),
    "diamond4": (4, [(0, 1), (1, 2), (0, 2), (0, 3), (2, 3)]),
    "complete4": (4, [(i, j) for i in range(4) for j in range(i+1, 4)]),
}
PARAMETERS = (F(1, 5), F(1, 3), F(1, 2), F(2, 3), F(4, 5))


def walk_distributions(n: int, edges: list, max_steps: int):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(not ns for ns in adj):
        raise ValueError("walk graphs must have no isolated vertex")
    dist = [F(int(i == 0)) for i in range(n)]
    yield dist
    for _ in range(max_steps):
        new = [F(0) for _ in range(n)]
        for u, mass in enumerate(dist):
            new[u] += mass/2
            for v in adj[u]:
                new[v] += mass/(2*len(adj[u]))
        assert sum(new) == 1
        dist = new
        yield dist


def root_connected(n: int, edges: list, mask: int) -> tuple[bool, ...]:
    adj = [[] for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        if (mask >> e) & 1:
            adj[u].append(v)
            adj[v].append(u)
    seen = {0}
    todo = [0]
    while todo:
        for v in adj[todo.pop()]:
            if v not in seen:
                seen.add(v)
                todo.append(v)
    return tuple(v in seen for v in range(n))


def russo_checks() -> dict:
    comparisons = configurations = 0
    for name, (n, edges) in GRAPHS.items():
        m = len(edges)
        con = [root_connected(n, edges, mask) for mask in range(1 << m)]
        pivots = []
        for mask in range(1 << m):
            row = [0]*n
            for e in range(m):
                if (mask >> e) & 1:
                    after = con[mask ^ (1 << e)]
                    for y in range(n):
                        row[y] += int(con[mask][y] and not after[y])
            pivots.append(row)
        configurations += 1 << m
        for dist in walk_distributions(n, edges, 5):
            for p in PARAMETERS:
                a = derivative = open_pivotal_expectation = F(0)
                for mask in range(1 << m):
                    k = mask.bit_count()
                    weight = p**k*(1-p)**(m-k)
                    event_prob = sum(dist[y] for y in range(n) if con[mask][y])
                    expected_n = sum(dist[y]*pivots[mask][y] for y in range(n))
                    a += weight*event_prob
                    derivative += weight*(F(k)/p-F(m-k)/(1-p))*event_prob
                    open_pivotal_expectation += weight*expected_n
                assert a > 0, name
                assert open_pivotal_expectation == p*derivative, (name, p)
                assert open_pivotal_expectation/(p*a) == derivative/a
                comparisons += 2
    return {"graphs": list(GRAPHS), "distinct_edge_configurations": configurations,
            "exact_identity_assertions": comparisons,
            "walk_steps": "0 through 5", "parameters": [str(p) for p in PARAMETERS]}


def toy_sampling_checks() -> dict:
    comparisons = configurations = 0
    for name, (n, edges) in GRAPHS.items():
        configurations += 1 << n
        for t in PARAMETERS:
            tau = [F(0)]*n
            for mask in range(1 << n):
                k = mask.bit_count()
                weight = t**k*(1-t)**(n-k)
                for y in range(n):
                    equivalent = y == 0 or ((mask & 1) and ((mask >> y) & 1))
                    tau[y] += weight*int(bool(equivalent))
            for y in range(n):
                assert tau[y] == (F(1) if y == 0 else t*t)
                comparisons += 1
            for dist in walk_distributions(n, edges, 8):
                sampled = sum(dist[y]*tau[y] for y in range(n))
                assert sampled == t*t+(1-t*t)*dist[0]
                comparisons += 1
    return {"finite_site_configurations": configurations,
            "exact_identity_assertions": comparisons,
            "walk_steps": "0 through 8"}


def peak_checks() -> dict:
    checks = 0
    for k in range(2, 62):
        t = F(1, k)
        r = t*t/(1+t*t)
        denominator = r+(1-r)*t*t
        first = 2*t*(1-r)/denominator
        second = 2*(1-r)*(r-(1-r)*t*t)/denominator**2
        assert first == 1/t
        assert second == 0
        assert first*first == (1-r)/r
        # Exact cross multiplication establishes the global maximum:
        # (r+(1-r)u^2)^2 - 4r(1-r)u^2 = (r-(1-r)u^2)^2.
        for u in (F(0), F(1, 5), F(1, 2), F(4, 5), F(1)):
            assert ((r+(1-r)*u*u)**2-4*r*(1-r)*u*u
                    == (r-(1-r)*u*u)**2)
            checks += 1
        checks += 3
    return {"rational_peak_instances": 60, "exact_identity_assertions": checks}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"research/artifacts/spectral-spike-replay.json")
    args = parser.parse_args()
    result = {
        "status": "PASS",
        "scope": "Exact finite algebra and combinatorics only; not infinite proofs or either universal conjecture.",
        "sign_covariance": partition_sign_checks(),
        "finite_volume_russo": russo_checks(),
        "toy_partition_sampling": toy_sampling_checks(),
        "toy_peak_calculus": peak_checks(),
    }
    result["total_exact_identity_assertions"] = sum(
        value["exact_identity_assertions"] for value in result.values()
        if isinstance(value, dict) and "exact_identity_assertions" in value
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
