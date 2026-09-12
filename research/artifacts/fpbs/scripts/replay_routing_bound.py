#!/usr/bin/env python3
"""Check only finite deterministic ingredients of the routing-tail bound.

Does not prove any infinite/unimodular/cost assertion or either conjecture.
Requires networkx. All inequality comparisons use integer arithmetic.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
import networkx as nx


def subgraph(vertices: list[int], edges: list[tuple[int, int]], mask: int) -> nx.Graph:
    graph = nx.Graph()
    graph.add_nodes_from(vertices)
    graph.add_edges_from(edge for i, edge in enumerate(edges) if mask & (1 << i))
    return graph


def check_graph(name: str, graph: nx.Graph) -> dict[str, int | str]:
    vertices = sorted(graph.nodes())
    edges = sorted(tuple(sorted(e)) for e in graph.edges())
    degrees = {graph.degree(v) for v in vertices}
    if len(degrees) != 1:
        raise ValueError('This replay uses regular graphs only.')
    d = degrees.pop()
    n = len(vertices)
    all_dist = dict(nx.all_pairs_shortest_path_length(graph))
    diameter = nx.diameter(graph)
    radii = list(range(1, min(3, diameter) + 1))
    balls = {R: {v: {w for w, length in all_dist[v].items() if length <= R}
                 for v in vertices} for R in radii}
    for R in radii:
        if len({len(balls[R][v]) for v in vertices}) != 1:
            raise ValueError('Ball sizes must agree for this averaging check.')
    configurations = vertex_tests = averaged_tests = 0
    for hmask in range(1 << len(edges)):
        H = subgraph(vertices, edges, hmask)
        if not nx.is_connected(H):
            continue
        distances = dict(nx.all_pairs_shortest_path_length(H))
        qmask = hmask
        while True:
            Q = subgraph(vertices, edges, qmask)
            component = {}
            for index, C in enumerate(nx.connected_components(Q)):
                component.update({v: index for v in C})
            D = {e for i, e in enumerate(edges)
                 if hmask & (1 << i) and not qmask & (1 << i)}
            cut_total = sum(component[v] != component[w]
                            for v in vertices for w in graph[v])
            for R in radii:
                long_total = 0
                incidence_total = 0
                for v in vertices:
                    b = sum(component[v] != component[w] for w in graph[v])
                    long_count = sum(distances[v][w] > R for w in graph[v])
                    local_deleted = sum(x in balls[R][v] and y in balls[R][v]
                                        for x, y in D)
                    # Pointwise b/d <= long_count/d + 1{some deleted edge in ball}.
                    assert b <= long_count + d * int(local_deleted > 0)
                    long_total += long_count
                    incidence_total += local_deleted
                    vertex_tests += 1
                B = len(balls[R][vertices[0]])
                # Each fixed deleted edge is internal to at most B rooted R-balls.
                assert incidence_total <= B * len(D)
                # Root averaging of the preceding witness inequality, cleared of fractions.
                assert cut_total <= long_total + d * B * len(D)
                averaged_tests += 1
            configurations += 1
            if qmask == 0:
                break
            qmask = (qmask - 1) & hmask
    return {'graph': name, 'vertices': n, 'edges': len(edges),
            'nested_configurations': configurations,
            'pointwise_checks': vertex_tests,
            'averaged_checks': averaged_tests}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    examples = [('cycle4', nx.cycle_graph(4)), ('cycle5', nx.cycle_graph(5)),
                ('complete4', nx.complete_graph(4)),
                ('complete_bipartite_3_3', nx.complete_bipartite_graph(3, 3))]
    results = [check_graph(name, graph) for name, graph in examples]
    result = {'passed': True,
              'scope': 'Finite witness and incidence-counting inequalities only; not an infinite proof.',
              'results': results,
              'totals': {key: sum(int(row[key]) for row in results)
                         for key in ['nested_configurations', 'pointwise_checks', 'averaged_checks']}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
