#!/usr/bin/env python3
"""Exact finite transcript and stopping-rule checks; run on MSI only."""

from collections import defaultdict, deque
from fractions import Fraction as F
import itertools
import json

from replay_critical_quotient import blocks
from exploration_search import balanced_search, verify_certificate


def explore(n, edges, bits, source, target, reverse=False, direction=0):
    adjacency = [[] for _ in range(n)]
    edge_indices = {tuple(sorted(edge)): i for i, edge in enumerate(edges)}
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    distances = {}
    for goal in {target, source}:
        dist, pending = {goal: 0}, deque([goal])
        while pending:
            u = pending.popleft()
            for v in adjacency[u]:
                if v not in dist:
                    dist[v] = dist[u]+1
                    pending.append(v)
        assert len(dist) == n
        distances[goal] = dist
    result = balanced_search(source, target, lambda u: adjacency[u],
                             lambda u, goal: distances[goal][u],
                             lambda edge: bits[edge_indices[edge]],
                             direction=direction, query_limit=len(edges), reverse=reverse)
    verify_certificate(result, source, target, lambda u: adjacency[u])
    assert result["status"] != "censored"
    return result["status"] == "connected", result["trace"]


def check(n, edges, source, target, reverse, direction, c, q):
    laws = {p: defaultdict(F) for p in (c, q)}
    outputs = {}
    d = max(sum(v in e for e in edges) for v in range(n))
    configurations = 0
    for bits in itertools.product((0, 1), repeat=len(edges)):
        output, trace = explore(n, edges, bits, source, target, reverse, direction)
        partition = blocks(n, edges, bits)
        source_cell = next(cell for cell in partition if source in cell)
        target_cell = next(cell for cell in partition if target in cell)
        assert output == (target in source_cell)
        assert len({e for e, _ in trace}) == len(trace)
        assert len(trace) <= 2*d*min(len(source_cell), len(target_cell))+1
        assert trace not in outputs or outputs[trace] == output
        outputs[trace] = output
        for p in (c, q):
            laws[p][trace] += p**sum(bits)*(1-p)**(len(edges)-sum(bits))
        configurations += 1
    for p, law in laws.items():
        assert sum(law.values()) == 1
        expected_queries = sum(prob*len(trace) for trace, prob in law.items())
        expected_open = sum(prob*sum(b for _, b in trace) for trace, prob in law.items())
        assert expected_open == p*expected_queries
        for trace, probability in law.items():
            opened = sum(b for _, b in trace)
            assert probability == p**opened*(1-p)**(len(trace)-opened)
    for trace, probability in laws[q].items():
        opened = sum(b for _, b in trace)
        # Exact likelihood ratio underlying the relative entropy identity.
        assert probability/laws[c][trace] == (q/c)**opened*((1-q)/(1-c))**(len(trace)-opened)
    assert sum(prob for trace, prob in laws[q].items() if outputs[trace]) >= sum(
        prob for trace, prob in laws[c].items() if outputs[trace])
    return configurations, len(outputs)


def main():
    path_neighbors = lambda v: [w for w in range(3) if abs(v-w) == 1]
    for cap in (0, 1, 2):
        result = balanced_search(0, 2, path_neighbors, lambda u, v: abs(u-v),
                                 lambda edge: True, direction=2, query_limit=cap)
        verify_certificate(result, 0, 2, path_neighbors)
        assert result["status"] == ("connected" if cap == 2 else "censored")
        assert len(result["trace"]) == cap
    isolated = balanced_search(0, 2, path_neighbors, lambda u, v: abs(u-v),
                               lambda edge: False, direction=2, query_limit=1)
    verify_certificate(isolated, 0, 2, path_neighbors)
    assert isolated["status"] == "disconnected"
    configurations = transcripts = cases = 0
    graphs = [(3, [(0, 1), (1, 2)]),
              (3, [(0, 1), (1, 2), (0, 2)]),
              (4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
              (4, list(itertools.combinations(range(4), 2))),
              (4, [(0, 1), (1, 2), (0, 2), (2, 3)])]
    for n, edges in graphs:
        for source, target in itertools.combinations(range(n), 2):
            for reverse in (False, True):
                for direction in (0, 1, 2):
                    for c, q in [(F(1, 3), F(1, 2)), (F(1, 2), F(3, 4))]:
                        count, traces = check(n, edges, source, target, reverse, direction, c, q)
                        configurations += count
                        transcripts += traces
                        cases += 1
        assert explore(n, edges, [0]*len(edges), 0, 0) == (True, ())
    print(json.dumps({"status": "passed", "arithmetic": "exact rational",
                      "scope": "Finite transcript likelihoods, Wald identities and stopping bounds; not an infinite proof",
                      "target_distance_weights": [0, 1, 2],
                      "cases": cases, "configurations": configurations,
                      "terminal_transcripts": transcripts}, indent=2))


if __name__ == '__main__':
    main()
