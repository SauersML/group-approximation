#!/usr/bin/env python3
"""Exact wall barriers and Bernoulli certificate-budget checks. Run on MSI."""

from collections import Counter, defaultdict
from fractions import Fraction as F
import itertools
import json
import time

from exploration_search import balanced_search, verify_certificate
from pilot_exploration_search import neighbors, distance
from exploration_search import edge_key


def is_wall_edge(edge, radius):
    (u, height), (v, other_height) = edge
    return height == other_height and abs(height) <= radius and {u, v} == {b"", bytes([0])}


def square_through(edge, radius):
    """Explicit open square, including crossing edges just outside the wall."""
    u, v = edge
    if u[1] == v[1]:
        crossing = {u[0], v[0]} == {b"", bytes([0])}
        step = -1 if crossing and u[1] < 0 else 1
        cycle = (u, v, (v[0], v[1]+step), (u[0], u[1]+step))
    else:
        assert u[0] == v[0]
        w = next(w for w in neighbors(u)
                 if w[1] == u[1] and {u[0], w[0]} != {b"", bytes([0])})
        cycle = (u, v, (w[0], v[1]), w)
    assert len(set(cycle)) == 4
    for a, b in zip(cycle, cycle[1:]+cycle[:1]):
        assert b in neighbors(a)
        assert not is_wall_edge(edge_key(a, b), radius)


def check_boundaries(radius):
    cells, frontier = {((b"", 0))}, {((b"", 0))}
    for depth in range(4):
        boundary = volume = 0
        for u in cells:
            for v in neighbors(u):
                if not is_wall_edge(edge_key(u, v), radius):
                    volume += 1
                    boundary += v not in cells
        assert boundary >= 2*len(cells)
        assert 3*boundary >= volume
        if depth < 3:
            frontier = {v for u in frontier for v in neighbors(u)}-cells
            cells.update(frontier)


def branch_checks():
    # Exhaust the 12 edges of a rooted ternary tree truncated at depth two.
    edges = [(0, child) for child in (1, 2, 3)]
    for parent in (1, 2, 3):
        edges.extend((parent, 3*parent+offset) for offset in (1, 2, 3))
    counts = Counter()
    for bits in itertools.product((0, 1), repeat=len(edges)):
        reached = {0}
        for (u, v), bit in zip(edges, bits):
            if bit and u in reached:
                reached.add(v)
        counts[(len(reached), sum(bits))] += 1
    rows = []
    for q in (F(1, 5), F(1, 3), F(1, 2), F(4, 5)):
        law = defaultdict(F)
        for (size, opened), count in counts.items():
            law[size] += count*q**opened*(1-q)**(12-opened)
        assert sum(law.values()) == 1
        mean = sum(size*prob for size, prob in law.items())
        assert mean == sum((3*q)**r for r in range(3))
        mean_min = sum(sum(prob for size, prob in law.items() if size >= k)**2
                       for k in range(1, 14))
        assert 1 <= mean_min <= mean
        a, b = (1-q)**2, 3*q
        assert F(4, 9)-a*b == (1-3*q)**2*(4-3*q)/9
        exact_sum = 3*(1-q)**3/((2-q)*(1-3*q*(1-q)**2))
        partial = sum((1-q)**(2*m+1)*sum((3*q)**r for r in range(1, m+1))
                      for m in range(33))
        assert 0 <= partial <= exact_sum <= F(27, 5)
        rows.append({"q": str(q), "depth_two_mean": str(mean),
                     "depth_two_independent_min_mean": str(mean_min),
                     "wall_branch_series": str(exact_sum)})
    return rows


def main():
    started = time.monotonic()
    source, target = (b"", 0), (bytes([0]), 0)
    rows = []
    squares_checked = 0
    for radius in range(8):
        check_boundaries(radius)
        checked_edges = set()
        lower_bound = 3**(radius+1)-radius-3
        for beta in (1, 2, 4):
            result = balanced_search(source, target, neighbors, distance,
                                     lambda edge: not is_wall_edge(edge, radius),
                                     direction=beta, query_limit=200000)
            verify_certificate(result, source, target, neighbors)
            assert result["status"] == "connected"
            queried = len(result["trace"])
            closed = sum(not bit for _, bit in result["trace"])
            for edge, bit in result["trace"]:
                if bit and edge not in checked_edges:
                    square_through(edge, radius)
                    checked_edges.add(edge)
                    squares_checked += 1
            assert queried >= lower_bound
            assert len(result["path"])-1 == 2*radius+3
            assert closed == 2*radius+1
            rows.append({"wall_radius": radius, "beta": beta, "queries": queried,
                         "proved_query_lower_bound": lower_bound,
                         "open_answers": queried-closed, "closed_answers": closed,
                         "certified_path_length": len(result["path"])-1,
                         "transcript_probability_at_one_half": "2^(-"+str(queried)+")"})
    print(json.dumps({"status": "passed", "graph": "T_4 x Z",
                      "scope": "Finite deterministic barrier runs and exact rational probability identities; not a near-critical query upper bound",
                      "barriers": rows, "branch_configurations": 4096,
                      "open_square_certificates": squares_checked,
                      "finite_boundary_checks": 32,
                      "bernoulli_checks": branch_checks(),
                      "elapsed_seconds": round(time.monotonic()-started, 3)}, indent=2))


if __name__ == '__main__':
    main()
