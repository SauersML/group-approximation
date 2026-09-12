#!/usr/bin/env python3
"""Exact search-envelope and all-open calibration checks. Run on MSI."""

from collections import deque
from fractions import Fraction
import itertools
import json

from exploration_search import balanced_search, edge_key, verify_certificate
from pilot_exploration_search import neighbors, distance


def distances(adjacency, root):
    result, queue = {root: 0}, deque([root])
    while queue:
        u = queue.popleft()
        for v in adjacency[u]:
            if v not in result:
                result[v] = result[u]+1
                queue.append(v)
    return result


def main():
    open_checks = envelope_checks = 0
    all_edges = list(itertools.combinations(range(4), 2))
    for selected in itertools.product((0, 1), repeat=len(all_edges)):
        edges = [edge for edge, keep in zip(all_edges, selected) if keep]
        adjacency = [[] for _ in range(4)]
        for u, v in edges:
            adjacency[u].append(v)
            adjacency[v].append(u)
        ambient = [distances(adjacency, root) for root in range(4)]
        if any(len(row) != 4 for row in ambient):
            continue
        for source, target in itertools.combinations(range(4), 2):
            for beta in (Fraction(3, 2), 2, 4):
                result = balanced_search(source, target, lambda u: adjacency[u],
                                         lambda u, v: ambient[v][u], lambda edge: True,
                                         direction=beta, query_limit=len(edges))
                verify_certificate(result, source, target, lambda u: adjacency[u])
                assert result["status"] == "connected"
                assert len(result["trace"]) <= 2*ambient[source][target]
                open_checks += 1
            for retained in itertools.product((0, 1), repeat=len(edges)):
                labels = dict(zip(edges, retained))
                open_adjacency = [[v for v in adjacent if labels[edge_key(u, v)]]
                                  for u, adjacent in enumerate(adjacency)]
                intrinsic = distances(open_adjacency, source)
                if target not in intrinsic:
                    continue
                length = intrinsic[target]
                result = balanced_search(source, target, lambda u: adjacency[u],
                                         lambda u, v: ambient[v][u], labels.__getitem__,
                                         direction=1, query_limit=len(edges))
                verify_certificate(result, source, target, lambda u: adjacency[u])
                assert result["status"] == "connected"
                ellipse = {u for u in range(4) if ambient[source][u]+ambient[target][u] <= length}
                induced = {edge for edge in edges if all(u in ellipse for u in edge)}
                assert {edge for edge, _ in result["trace"]} <= induced
                assert len(result["trace"]) <= len(induced)
                envelope_checks += 1
    origin = (b"", 0)
    volume_checks = 0
    for a, b, excess in itertools.product(range(4), repeat=3):
        target = (bytes([0])*a, b)
        radius = a+b+2*excess
        ellipse, pending = {origin}, deque([origin])
        while pending:
            u = pending.popleft()
            for v in neighbors(u):
                if v not in ellipse and distance(origin, v)+distance(v, target) <= radius:
                    ellipse.add(v)
                    pending.append(v)
        assert len(ellipse) == (a+2)*(b+2)*3**excess-(a+b+2*excess+3)
        volume_checks += 1
    calibration = []
    for length in (1, 2, 4, 8, 16, 32):
        target = (bytes([0])*length, length)
        row = {"side_length": length, "endpoint_distance": 2*length}
        for beta in (1, 2):
            result = balanced_search(origin, target, neighbors, distance, lambda edge: True,
                                     direction=beta, query_limit=30000)
            verify_certificate(result, origin, target, neighbors)
            assert result["status"] == "connected"
            queries = len(result["trace"])
            if beta == 1:
                assert queries >= length*(length+1)//2-1
            else:
                assert queries <= 4*length
            row["queries_beta_"+str(beta)] = queries
        calibration.append(row)
    print(json.dumps({"status": "passed", "arithmetic": "exact integer/rational",
                      "scope": "Finite algorithm and geometry checks; infinite bounds rely on the written proof",
                      "all_open_checks": open_checks, "ellipse_checks": envelope_checks,
                      "product_volume_checks": volume_checks, "calibration": calibration}, indent=2))


if __name__ == "__main__":
    main()
