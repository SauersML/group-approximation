#!/usr/bin/env python3
"""Bounded exact checks for cluster-contact-mergers.md. Run only on MSI."""

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import time


def components(n, opened):
    parent = list(range(n))

    def find(a):
        while a != parent[a]:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for a, b in opened:
        a, b = find(a), find(b)
        parent[a] = b
    return [find(a) for a in range(n)]


def statistics(n, edges, opened):
    labels = components(n, opened)
    contacts = Counter()
    for a, b in edges:
        a, b = labels[a], labels[b]
        if a != b:
            contacts[tuple(sorted((a, b)))] += 1
    blocks = sorted(set(labels))
    values = list(contacts.values())
    triangle = sum(contacts[a, b] * contacts[a, c] * contacts[b, c]
                   for a, b, c in combinations(blocks, 3))
    return (len(blocks), sum(values), sum(k*k for k in values),
            sum(k**3 for k in values), triangle,
            sum(k*(k-1)//2 for k in values),
            sum(k*k*(k-1)//2 for k in values))


def exhaustive():
    pairs = list(combinations(range(5), 2))
    states = transitions = 0
    for assignment in product(range(3), repeat=len(pairs)):
        edges = [e for e, s in zip(pairs, assignment) if s]
        opened = [e for e, s in zip(pairs, assignment) if s == 2]
        closed = [e for e, s in zip(pairs, assignment) if s == 1]
        initial = statistics(5, edges, opened)
        actual = [0, 0, 0, 0]
        for edge in closed:
            after = statistics(5, edges, opened + [edge])
            for j, index in enumerate((0, 1, 2, 5)):
                actual[j] += after[index] - initial[index]
            transitions += 1
        _, m, q, r, t, _, h3 = initial
        expected = [-m, -q, -r + 6*t, -h3 + 3*t]
        assert actual == expected, (assignment, actual, expected)
        states += 1
    return {'labeled_vertices': 5, 'three_state_assignments': states,
            'individual_closed_edge_openings': transitions}


def check_density(n, edges, p):
    second = Fraction(0)
    contact_rhs = Fraction(0)
    m = len(edges)
    for mask in range(1 << m):
        opened = [e for j, e in enumerate(edges) if mask & (1 << j)]
        k = len(opened)
        count, first, square, *_ = statistics(n, edges, opened)
        weight = p**k * (1-p)**(m-k)
        factor = (k*(k-1)/p**2 - 2*k*(m-k)/(p*(1-p))
                  + (m-k)*(m-k-1)/(1-p)**2)
        second += count * weight * factor
        contact_rhs += (square-first)*weight/(1-p)**2
    assert second == contact_rhs, (n, edges, p, second, contact_rhs)
    return str(second/n)


def tree_ball(degree, radius):
    edges = []
    frontier = [0]
    size = 1
    for level in range(radius):
        next_frontier = []
        for v in frontier:
            for _ in range(degree if level == 0 else degree-1):
                edges.append((v, size))
                next_frontier.append(size)
                size += 1
        frontier = next_frontier
    return size, edges


def dispersion(n, edges, opened):
    labels = components(n, opened)
    root = labels[0]
    contact = Counter()
    for a, b in edges:
        a, b = labels[a], labels[b]
        if a == root and b != root:
            contact[b] += 1
        elif b == root and a != root:
            contact[a] += 1
    total = sum(contact.values())
    square = sum(k*k for k in contact.values())
    return Fraction(total*total, square) if square else Fraction(0)


def initial_drift(n, edges):
    initial = dispersion(n, edges, [])
    # Open every edge of the finite host separately, including edges whose
    # increment is zero. No use of the analytical common-neighbor formula.
    drift = sum((dispersion(n, edges, [e])-initial for e in edges), Fraction(0))
    return initial, drift


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    exhaustive_result = exhaustive()
    prism = [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5),
             (0, 3), (1, 4), (2, 5)]
    bipartite = [(a, b) for a in range(3) for b in range(3, 6)]
    examples = {'prism': (6, prism), 'K33': (6, bipartite),
                'K5': (5, list(combinations(range(5), 2))),
                'path5': (5, [(i, i+1) for i in range(4)]),
                'cycle5': (5, [(i, (i+1) % 5) for i in range(5)]),
                'parallel3': (2, [(0, 1)]*3)}
    density = {name: {str(p): check_density(n, edges, p)
                      for p in (Fraction(1, 3), Fraction(2, 3))}
               for name, (n, edges) in examples.items()}
    nonclosure = {}
    for name in ('prism', 'K33'):
        n, edges = examples[name]
        s = statistics(n, edges, [])
        nonclosure[name] = {'N_M_Q_R': list(s[:4]), 'T': s[4],
                            'Q_generator': -s[3]+6*s[4]}
    assert nonclosure['prism']['Q_generator'] == 3
    assert nonclosure['K33']['Q_generator'] == -9
    n, edges = tree_ball(13, 2)
    tree_initial, tree_drift = initial_drift(n, edges)
    base_n, base_edges = tree_ball(4, 2)
    product_edges = [(10*a+j, 10*b+j) for a, b in base_edges for j in range(10)]
    product_edges += [(10*a+i, 10*a+j) for a in range(base_n)
                     for i, j in combinations(range(10), 2)]
    product_initial, product_drift = initial_drift(10*base_n, product_edges)
    assert tree_initial == product_initial == 13
    assert tree_drift == 143
    assert product_drift == Fraction(-29, 5)
    root = Path(__file__).resolve().parents[4]
    source_paths = [Path(__file__).resolve(),
                    root/'research/artifacts/fpbs/docs/cluster-contact-mergers.md']
    report = {
        'status': 'passed',
        'execution': 'MSI acn112; one process, shared project storage',
        'scope': 'Exact finite algebra and local generator examples only; no threshold proof.',
        'exhaustive': exhaustive_result,
        'finite_density_second_derivatives': density,
        'moment_nonclosure': nonclosure,
        'initial_root_dispersion': {'both': '13', 'T13_drift': str(tree_drift),
                                   'T4_times_K10_drift': str(product_drift)},
        'source_sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in source_paths},
        'elapsed_seconds': round(time.monotonic()-start, 3),
    }
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
