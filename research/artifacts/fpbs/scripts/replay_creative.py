#!/usr/bin/env python3
"""Exact finite audits for research reductions, not tests of infinite conjectures.
Requires sympy and networkx. Run: python replay_creative.py [--output FILE]
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction
from pathlib import Path
import networkx as nx
import sympy as sp


def connected_matrix(graph: nx.Graph, n: int) -> list[list[int]]:
    labels = {}
    for i, comp in enumerate(nx.connected_components(graph)):
        for v in comp:
            labels[v] = i
    return [[int(labels[i] == labels[j]) for j in range(n)] for i in range(n)]


def check_russo(graph: nx.Graph) -> dict:
    graph = nx.convert_node_labels_to_integers(graph)
    n, m = graph.number_of_nodes(), graph.number_of_edges()
    if m > 16:
        raise ValueError('This exhaustive audit is restricted to at most 16 edges.')
    edges = list(graph.edges())
    # Count connections and OPEN pivotal edges at each number of open edges.
    counts = [[[0] * (m + 1) for _ in range(n)] for _ in range(n)]
    pivots = [[[0] * (m + 1) for _ in range(n)] for _ in range(n)]
    for mask in range(1 << m):
        g = nx.Graph()
        g.add_nodes_from(range(n))
        g.add_edges_from(e for i, e in enumerate(edges) if mask >> i & 1)
        k = g.number_of_edges()
        conn = connected_matrix(g, n)
        for i in range(n):
            for j in range(n):
                counts[i][j][k] += conn[i][j]
        for e in list(nx.bridges(g)):
            g.remove_edge(*e)
            after = connected_matrix(g, n)
            g.add_edge(*e)
            for i in range(n):
                for j in range(n):
                    pivots[i][j][k] += conn[i][j] - after[i][j]
    p = sp.Symbol('p')
    for i in range(n):
        for j in range(n):
            tau = sum(counts[i][j][k] * p**k * (1-p)**(m-k) for k in range(m+1))
            joint = sum(pivots[i][j][k] * p**k * (1-p)**(m-k) for k in range(m+1))
            assert sp.expand(joint - p * sp.diff(tau, p)) == 0
    return {'vertices': n, 'edges': m, 'configurations': 1 << m,
            'ordered_pair_polynomial_identities': n*n}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    mergers = 0
    for a in range(1,9):
        for b in range(1,9):
            n = a+b
            old = sp.diag(sp.ones(a)/a, sp.ones(b)/b)
            new = sp.ones(n)/n
            w = sp.Matrix([sp.Rational(1,a)]*a + [-sp.Rational(1,b)]*b)
            diff = sp.Rational(a*b, a+b) * w*w.T
            assert old-new == diff
            assert diff*diff == diff
            assert sp.trace(diff) == 1
            mergers += 1
    T = sp.Matrix([[16,9,7,9],[9,16,9,7],[7,9,16,9],[9,7,9,16]])/16
    assert T.inv()[0,2] == sp.Rational(16,1845)
    graphs = {
        'path_4': nx.path_graph(4),
        'cycle_4': nx.cycle_graph(4),
        'cycle_5': nx.cycle_graph(5),
        'complete_4': nx.complete_graph(4),
        'diamond': nx.complete_graph(4),
        'ladder_3': nx.ladder_graph(3),
        'two_triangles_at_a_cutvertex': nx.Graph([(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]),
    }
    graphs['diamond'].remove_edge(0,1)
    audit = {name: check_russo(g) for name,g in graphs.items()}
    result = {
        'status': 'PASS',
        'scope': 'Exact finite algebra only. No infinite theorem or conjecture is computationally certified.',
        'rank_one_mergers': mergers,
        'c4_positive_inverse_entry': str(T.inv()[0,2]),
        'russo_audits': audit,
        'total_configurations': sum(a['configurations'] for a in audit.values()),
        'total_polynomial_identities': sum(a['ordered_pair_polynomial_identities'] for a in audit.values()),
        'universal_pivotal_bound': 'OPEN',
        'dyadic_operator_estimate': 'OPEN',
        'sparse_fiid_spines_for_all_infinite_kazhdan_groups': 'OPEN',
        'positive_rank_gradient_kazhdan_farber_chain': 'OPEN',
    }
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text+'\n')
    print(text)

if __name__ == '__main__':
    main()
