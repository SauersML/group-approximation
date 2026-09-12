#!/usr/bin/env python3
"""Exact finite checks supporting the accompanying mathematical arguments.

These tests do NOT verify infinite percolation, measurability, the Abért--Weiss
or Gaboriau theorems, or either universal conjecture. Standard library only.
"""
from __future__ import annotations
import argparse
from collections import deque
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path

Edge = tuple[int, int]

def edge(u: int, v: int) -> Edge:
    return (min(u, v), max(u, v))

def components(n: int, edges: set[Edge]) -> tuple[list[set[int]], list[int]]:
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    parts: list[set[int]] = []
    index = [-1] * n
    for root in range(n):
        if index[root] >= 0:
            continue
        k = len(parts)
        part = {root}
        index[root] = k
        todo = [root]
        while todo:
            u = todo.pop()
            for v in adj[u]:
                if index[v] < 0:
                    index[v] = k
                    part.add(v)
                    todo.append(v)
        parts.append(part)
    return parts, index

def forest(n: int, edges: set[Edge]) -> set[Edge]:
    parent = list(range(n))
    def root(u: int) -> int:
        while parent[u] != u:
            parent[u] = parent[parent[u]]
            u = parent[u]
        return u
    result: set[Edge] = set()
    for u, v in sorted(edges):
        ru, rv = root(u), root(v)
        if ru != rv:
            parent[ru] = rv
            result.add((u, v))
    return result

def distances(n: int, edges: set[Edge], sources: set[int]) -> list[int]:
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    dist = [-1] * n
    todo = deque(sorted(sources))
    for u in sources:
        dist[u] = 0
    while todo:
        u = todo.popleft()
        for v in adj[u]:
            if dist[v] < 0:
                dist[v] = dist[u] + 1
                todo.append(v)
    return dist

def graphs() -> list[tuple[str, int, set[Edge]]]:
    return [
        ('path4', 4, {(0, 1), (1, 2), (2, 3)}),
        ('cycle4', 4, {(0, 1), (1, 2), (2, 3), (0, 3)}),
        ('cycle6', 6, {edge(i, (i + 1) % 6) for i in range(6)}),
        ('complete4', 4, set(combinations(range(4), 2))),
        ('ladder3x2', 6, {(0, 1), (1, 2), (3, 4), (4, 5),
                            (0, 3), (1, 4), (2, 5)}),
    ]

def check_reconnection() -> dict[str, int]:
    counts: dict[str, int] = {}
    for name, n, ambient in graphs():
        edges = sorted(ambient)
        count = 0
        # State 0: p-closed; state 1: in (q,p]; state 2: q-open.
        for states in product(range(3), repeat=len(edges)):
            q_edges = {e for e, s in zip(edges, states) if s == 2}
            band = {e for e, s in zip(edges, states) if s == 1}
            p_edges = q_edges | band
            q_parts, _ = components(n, q_edges)
            p_parts, p_index = components(n, p_edges)
            h_edges = forest(n, q_edges) | band
            h_parts, _ = components(n, h_edges)
            assert {frozenset(c) for c in h_parts} == {frozenset(c) for c in p_parts}
            sink_id = p_index[0]
            sink = p_parts[sink_id]
            dist = distances(n, ambient, sink)
            bridges: set[Edge] = set()
            for k, part in enumerate(p_parts):
                if k == sink_id:
                    continue
                height = min(dist[u] for u in part)
                assert height > 0
                choices = []
                for u, v in edges:
                    if u in part and dist[u] == height and dist[v] == height - 1:
                        choices.append((u, v))
                    if v in part and dist[v] == height and dist[u] == height - 1:
                        choices.append((v, u))
                assert choices
                u, v = min(choices)
                assert v not in part
                b = edge(u, v)
                assert b not in p_edges and b not in bridges
                bridges.add(b)
            assert len(bridges) == len(p_parts) - 1
            assert len(components(n, h_edges | bridges)[0]) == 1
            assert len(h_edges | bridges) == n - len(q_parts) + len(band) + len(p_parts) - 1
            count += 1
        counts[name] = count
    return counts

def check_ball_bound() -> dict[str, int]:
    counts: dict[str, int] = {}
    for name, n, ambient in graphs():
        edges = sorted(ambient)
        count = 0
        for root in range(n):
            dist = distances(n, ambient, {root})
            for radius in range(max(dist) + 1):
                ball = {v for v in range(n) if dist[v] <= radius}
                for states in product(range(2), repeat=len(edges)):
                    opened = {e for e, s in zip(edges, states) if s}
                    full_parts, full_index = components(n, opened)
                    restricted = {e for e in opened if e[0] in ball and e[1] in ball}
                    ball_parts, ball_index = components(n, restricted)
                    full = full_parts[full_index[root]]
                    local = ball_parts[ball_index[root]]
                    delta = Fraction(1, len(local)) - Fraction(1, len(full))
                    assert 0 <= delta <= Fraction(1, radius + 1)
                    if full <= ball:
                        assert delta == 0
                    count += 1
        counts[name] = count
    return counts

def check_routing_formula() -> dict[str, object]:
    cases = 0
    samples = []
    for r in range(2, 6):
        for k in range(1, 11):
            eps = Fraction(1, 2**k)
            a = 1 - eps
            # Exact finite sum plus its exact infinite geometric remainder.
            cutoff = 25
            e_m = sum((a ** (2*m + 1) for m in range(cutoff)), Fraction(0))
            e_m += a ** (2*cutoff + 1) / (1 - a*a)
            assert e_m == (1-eps) / (eps * (2-eps))
            e_d = 1 + 2*e_m
            assert e_d == (2-eps*eps) / (eps*(2-eps))
            scaled = r * eps * e_d
            assert scaled - r == r * eps * (1-eps) / (2-eps)
            assert scaled > r
            cases += 1
            if r == 2 and k in (1, 4, 8, 10):
                samples.append({'rank': r, 'epsilon': str(eps),
                                'expected_distance': str(e_d),
                                'excess_times_expected_distance': str(scaled)})
    return {'exact_parameter_cases': cases, 'samples': samples}

def check_tree_sharpness() -> int:
    count = 0
    for r in range(2, 51):
        pc, pu = Fraction(1, 2*r-1), Fraction(1)
        kappa_pc = 1-r*pc
        assert r*(pu-pc)-kappa_pc == r-1
        count += 1
    return count

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    reconnection = check_reconnection()
    ball_bound = check_ball_bound()
    data = {
        'status': 'PASS',
        'verification_scope': 'Exact finite combinatorics and rational identities only; not a formal proof of the infinite results or either conjecture.',
        'reconnection_configurations': reconnection,
        'reconnection_total': sum(reconnection.values()),
        'finite_ball_configurations': ball_bound,
        'finite_ball_total': sum(ball_bound.values()),
        'routing': check_routing_formula(),
        'regular_tree_sharpness_ranks': check_tree_sharpness(),
    }
    text = json.dumps(data, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')

if __name__ == '__main__':
    main()
