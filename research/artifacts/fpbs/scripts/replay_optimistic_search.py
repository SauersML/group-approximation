#!/usr/bin/env python3
"""Exact lazy path-search checks and a bounded implicit-graph pilot. MSI only."""

from collections import defaultdict, deque
from fractions import Fraction as F
import hashlib
import itertools
import json
import random
import time

from exploration_search import optimistic_search, verify_certificate, edge_key
from pilot_exploration_search import neighbors, distance, encode
from replay_search_barriers import is_wall_edge


def graph_distances(adjacency, root):
    distances, queue = {root: 0}, deque([root])
    while queue:
        u = queue.popleft()
        for v in adjacency[u]:
            if v not in distances:
                distances[v] = distances[u]+1
                queue.append(v)
    return distances


def verify_growth(result, source):
    reached = {source}
    for (u, v), bit in result["trace"]:
        assert (u in reached) != (v in reached)
        if bit:
            reached.update((u, v))
    assert len(reached)-1 == sum(bit for _, bit in result["trace"])


def finite_checks():
    graphs = [(3, [(0, 1), (1, 2)]),
              (3, [(0, 1), (1, 2), (0, 2)]),
              (4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
              (4, list(itertools.combinations(range(4), 2)))]
    cases = configurations = transcripts = 0
    for size, edges in graphs:
        adjacency = [[] for _ in range(size)]
        for u, v in edges:
            adjacency[u].append(v)
            adjacency[v].append(u)
        indices = {edge_key(u, v): i for i, (u, v) in enumerate(edges)}
        for source, target in itertools.combinations(range(size), 2):
            ambient = graph_distances(adjacency, target)
            for cap in range(len(edges)+1):
                laws = {p: defaultdict(F) for p in (F(1, 3), F(1, 2))}
                outputs = {}
                for bits in itertools.product((0, 1), repeat=len(edges)):
                    result = optimistic_search(source, target, lambda u: adjacency[u],
                                               lambda u, goal: ambient[u],
                                               lambda edge: bits[indices[edge]],
                                               query_limit=cap, planning_limit=20000)
                    verify_certificate(result, source, target, lambda u: adjacency[u])
                    verify_growth(result, source)
                    assert result["censor_reason"] != "planning"
                    actual = [[v for v in adjacency[u] if bits[indices[edge_key(u, v)]]]
                              for u in range(size)]
                    shortest = graph_distances(actual, source).get(target)
                    if result["status"] == "connected":
                        assert len(result["path"])-1 == shortest
                        for (u, v), _ in result["trace"]:
                            assert graph_distances(adjacency, source)[u]+ambient[u] <= shortest
                            assert graph_distances(adjacency, source)[v]+ambient[v] <= shortest
                    if cap == len(edges):
                        assert result["status"] == ("connected" if shortest is not None else "disconnected")
                    trace = result["trace"]
                    assert trace not in outputs or outputs[trace] == result["status"]
                    outputs[trace] = result["status"]
                    for p in laws:
                        laws[p][trace] += p**sum(bits)*(1-p)**(len(edges)-sum(bits))
                    configurations += 1
                for p, law in laws.items():
                    assert sum(law.values()) == 1
                    queries = sum(prob*len(trace) for trace, prob in law.items())
                    opened = sum(prob*sum(bit for _, bit in trace) for trace, prob in law.items())
                    assert opened == p*queries
                    for trace, prob in law.items():
                        opened = sum(bit for _, bit in trace)
                        assert prob == p**opened*(1-p)**(len(trace)-opened)
                cases += 1
                transcripts += len(outputs)
    simple = lambda u: [v for v in range(3) if abs(u-v) == 1]
    for query_cap, planning_cap, reason in ((0, 100, "queries"), (2, 0, "planning")):
        result = optimistic_search(0, 2, simple, lambda u, v: abs(u-v), lambda e: True,
                                   query_limit=query_cap, planning_limit=planning_cap)
        verify_certificate(result, 0, 2, simple)
        assert result["status"] == "censored" and result["censor_reason"] == reason
    same = optimistic_search(0, 0, simple, lambda u, v: abs(u-v), lambda e: True,
                             query_limit=0, planning_limit=0)
    verify_certificate(same, 0, 0, simple)
    return {"cap_cases": cases, "configurations": configurations, "transcripts": transcripts}


def wall_checks():
    source, target = (b"", 0), (bytes([0]), 0)
    rows = []
    for radius in range(8):
        result = optimistic_search(source, target, neighbors, distance,
                                   lambda edge: not is_wall_edge(edge, radius),
                                   query_limit=200, planning_limit=500000)
        verify_certificate(result, source, target, neighbors)
        verify_growth(result, source)
        assert result["status"] == "connected"
        assert len(result["trace"]) == 5*radius+4
        assert len(result["path"])-1 == 2*radius+3
        assert sum(not bit for _, bit in result["trace"]) == 2*radius+1
        rows.append({"wall_radius": radius, "queries": len(result["trace"]),
                     "path_length": len(result["path"])-1,
                     "planning_expansions": result["planning_expansions"],
                     "replans": result["replans"]})
    return rows


def pilot():
    origin, records = (b"", 0), []
    for seed in range(4):
        rng = random.Random(1000003+seed)
        walk, endpoints = origin, {}
        for n in range(1, 97):
            step = rng.randrange(12)
            if step >= 6:
                walk = tuple(neighbors(walk))[step-6]
            if n in (48, 96):
                endpoints[n] = walk
        key = seed.to_bytes(16, "big")
        for n, target in endpoints.items():
            for percent in (60, 90):
                cutoff = percent*(1 << 64)//100

                def read_edge(edge):
                    label = int.from_bytes(hashlib.blake2b(encode(edge[0])+encode(edge[1]),
                                           key=key, digest_size=8).digest(), "big")
                    return label < cutoff

                result = optimistic_search(origin, target, neighbors, distance, read_edge,
                                           query_limit=400, planning_limit=8000)
                verify_certificate(result, origin, target, neighbors)
                verify_growth(result, origin)
                records.append({"seed": seed, "walk_length": n, "percent": percent,
                                "distance": distance(origin, target), "status": result["status"],
                                "censor_reason": result["censor_reason"],
                                "queries": len(result["trace"]),
                                "planning_expansions": result["planning_expansions"],
                                "replans": result["replans"],
                                "path_length": len(result["path"])-1 if result["path"] else None})
    return records


def main():
    start = time.monotonic()
    report = {"status": "passed", "scope": "Exact finite correctness and wall queries, plus a censored pseudorandom pilot; no universal expected-cost bound",
              "finite": finite_checks(), "walls": wall_checks(), "pilot": pilot(),
              "elapsed_seconds": round(time.monotonic()-start, 3)}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
