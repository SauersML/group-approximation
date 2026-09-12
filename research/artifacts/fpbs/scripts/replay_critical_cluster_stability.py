#!/usr/bin/env python3
"""Exact finite checks for critical-cluster-stability.md; execute on MSI only."""

import itertools
import json
from fractions import Fraction as Q


def component(edges, states, level):
    reached = {0}
    while True:
        previous = len(reached)
        for (u, v), state in zip(edges, states):
            if state <= level and (u in reached or v in reached):
                reached.update((u, v))
        if len(reached) == previous:
            return reached


def boundary_identity(edges, c, q):
    # State 0: open at c; state 1: opens in (c,q]; state 2: closed at q.
    weights = (c, q - c, 1 - q)
    delta = Q(0)
    expected = Q(0)
    total = Q(0)
    t = (q - c) / (1 - c)
    for states in itertools.product(range(3), repeat=len(edges)):
        weight = Q(1)
        for state in states:
            weight *= weights[state]
        critical = component(edges, states, 0)
        later = component(edges, states, 1)
        boundary = sum((u in critical) != (v in critical) for u, v in edges)
        total += weight
        delta += weight * (critical != later)
        expected += weight * (1 - (1 - t) ** boundary)
    assert total == 1
    assert delta == expected, (edges, c, q, delta, expected)
    return 3 ** len(edges)


def partitions(n):
    """Enumerate set partitions via restricted growth strings."""
    for labels in itertools.product(range(n), repeat=n):
        if labels[0] != 0:
            continue
        if any(labels[i] > 1 + max(labels[:i]) for i in range(1, n)):
            continue
        yield tuple(frozenset(i for i in range(n) if labels[i] == label)
                    for label in range(max(labels) + 1))


def coupled_sign_bound():
    all_partitions = list(partitions(4))
    cases = 0
    for earlier in all_partitions:
        for later in all_partitions:
            if not all(any(a <= b for b in later) for a in earlier):
                continue
            for rank in itertools.permutations(range(4)):
                for signs in itertools.product((-1, 1), repeat=4):
                    for root in range(4):
                        a = next(block for block in earlier if root in block)
                        b = next(block for block in later if root in block)
                        va = signs[min(a, key=lambda v: rank[v])]
                        vb = signs[min(b, key=lambda v: rank[v])]
                        # Individual squared differences can be 4; average signs.
                        assert (va - vb) ** 2 in (0, 4)
                        cases += 1
                for root in range(4):
                    a = next(block for block in earlier if root in block)
                    b = next(block for block in later if root in block)
                    selected_a = min(a, key=lambda v: rank[v])
                    selected_b = min(b, key=lambda v: rank[v])
                    sign_average = Q(sum(
                        (signs[selected_a] - signs[selected_b]) ** 2
                        for signs in itertools.product((-1, 1), repeat=4)), 16)
                    assert sign_average <= 2 * (a != b)
                    # The zero value for an infinite later cluster has squared
                    # difference 1. Its event is necessarily a change event.
                    assert Q(sum(signs[selected_a] ** 2 for signs in
                                 itertools.product((-1, 1), repeat=4)), 16) == 1
    return cases


def two_atom_control():
    cases = 0
    for rho in (Q(1, 2), Q(3, 4), Q(9, 10)):
        for s in (Q(1, 2), Q(1, 10), Q(1, 100)):
            atom_difference = {Q(1): s * s, rho: -s * s}
            assert sum(abs(mass) for mass in atom_difference.values()) == 2*s*s
            for n in range(41):
                moment = s*s + (1-s*s)*rho**n
                assert abs(moment - s*s - rho**n) / rho**n == s*s
                assert max(s*s, rho**n) <= moment <= s*s + rho**n
                cases += 1
    return cases


def main():
    graphs = [
        [(0, 1), (1, 2)],
        [(0, 1), (1, 2), (2, 0)],
        [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)],
    ]
    pairs = [(Q(1, 4), Q(1, 2)), (Q(1, 3), Q(2, 3)),
             (Q(2, 5), Q(2, 5)), (Q(2, 5), Q(9, 10))]
    configurations = sum(boundary_identity(edges, c, q)
                         for edges in graphs for c, q in pairs)
    print(json.dumps({
        "status": "passed",
        "boundary_configurations": configurations,
        "nested_partition_sign_cases": coupled_sign_bound(),
        "two_atom_moment_cases": two_atom_control(),
        "scope": "Exact finite rational checks only; no infinite theorem verification.",
    }, indent=2))


if __name__ == "__main__":
    main()
