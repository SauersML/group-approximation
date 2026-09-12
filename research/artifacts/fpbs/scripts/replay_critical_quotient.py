#!/usr/bin/env python3
"""Exact finite checks for critical-quotient-sprinkling.md. Run on MSI."""

import itertools
import json
from fractions import Fraction as Q
from math import comb

from replay_critical_cluster_stability import partitions


def blocks(n, edges, retained):
    labels = list(range(n))
    for (u, v), keep in zip(edges, retained):
        if keep:
            a, b = labels[u], labels[v]
            labels = [a if label == b else label for label in labels]
    return tuple(frozenset(v for v in range(n) if labels[v] == label)
                 for label in sorted(set(labels)))


def root_reaches(n, edges, retained):
    # An independent reachability calculation for the direct q-law.
    reached = {0}
    for _ in range(n):
        reached |= {v for (u, v), keep in zip(edges, retained) if keep and u in reached}
        reached |= {u for (u, v), keep in zip(edges, retained) if keep and v in reached}
    return n-1 in reached


def sprinkling_checks():
    graphs = [(3, [(0, 1), (1, 2), (0, 2)]),
              (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
              (4, list(itertools.combinations(range(4), 2)))]
    cases = 0
    for n, edges in graphs:
        for c, t in [(Q(1, 3), Q(1, 4)), (Q(2, 5), Q(1, 2))]:
            q = c+(1-c)*t
            direct, contracted = Q(0), Q(0)
            for retained in itertools.product((False, True), repeat=len(edges)):
                count = sum(retained)
                direct += (q**count * (1-q)**(len(edges)-count)
                           * root_reaches(n, edges, retained))
            for states in itertools.product(range(3), repeat=len(edges)):
                critical = blocks(n, edges, [s == 0 for s in states])
                cell = {v: i for i, block in enumerate(critical) for v in block}
                quotient_edges = [(cell[u], cell[v]) for u, v in edges]
                quotient = blocks(len(critical), quotient_edges, [s == 1 for s in states])
                expanded = {frozenset().union(*(critical[i] for i in block)) for block in quotient}
                assert expanded == set(blocks(n, edges, [s != 2 for s in states]))
                weight = Q(1)
                for state in states:
                    weight *= (c, (1-c)*t, (1-c)*(1-t))[state]
                contracted += weight * any(0 in b and n-1 in b for b in expanded)
                cases += 1
            assert direct == contracted
    for k in range(1, 9):
        t = Q(2, 7)
        probability = sum(t**sum(bits) * (1-t)**(k-sum(bits))
                          for bits in itertools.product((0, 1), repeat=k) if any(bits))
        assert probability == 1-(1-t)**k
        if k > 1:
            assert probability > t
    return cases


def palm_checks():
    count = 0
    for partition in partitions(4):
        n, k = 4, len(partition)
        masses = [len(block) for block in partition]
        degree = [m*(n-m) for m in masses]  # The quotient of the complete graph.
        kappa = sum(Q(m, n)/m for m in masses)
        assert kappa == Q(k, n)
        tilted = [Q(m, n)/m/kappa for m in masses]
        assert sum(tilted) == 1
        assert sum(w*m for w, m in zip(tilted, masses)) == 1/kappa
        original_mean_mass = sum(Q(m, n)*m for m in masses)
        assert sum(w*m*m for w, m in zip(tilted, masses)) == original_mean_mass/kappa
        f = [[masses[i]**2*(degree[j]+1) for j in range(k)] for i in range(k)]
        outgoing = sum(tilted[i]*sum(f[i]) for i in range(k))
        incoming = sum(tilted[j]*sum(f[i][j] for i in range(k)) for j in range(k))
        assert outgoing == incoming
        count += 1
    # A mass-three block and a singleton: the original root bias fails MTP.
    assert Q(3, 4)*3+Q(1, 4)*1 == Q(5, 2)
    assert Q(3, 4)*1+Q(1, 4)*3 == Q(3, 2)
    assert Q(1, 2)*3+Q(1, 2)*1 == Q(1, 2)*1+Q(1, 2)*3
    return count


def layer_cut_checks():
    sizes = [1, 2, 4, 8, 16]
    degrees = [2, 5, 10, 20, 40]
    cases = 0
    for selected in itertools.product(*(range(n+1) for n in sizes)):
        if not any(selected):
            continue
        boundary = sum(a*(sizes[k+1]-selected[k+1])+selected[k+1]*(sizes[k]-a)
                       for k, a in enumerate(selected[:-1])) + selected[-1]*32
        mass = sum(a*d for a, d in zip(selected, degrees))
        assert 5*boundary >= 3*mass
        cases += 1
    bipartite_cuts = 0
    for n in range(1, 33):
        for a in range(n+1):
            for b in range(2*n+1):
                j = a+b
                if 1 <= 2*j <= 3*n:
                    boundary = a*(2*n-b)+b*(n-a)
                    assert 4*boundary >= n*j
                    bipartite_cuts += 1
    return cases, bipartite_cuts


def finite_disconnection_checks():
    cases = 0
    for n in (1, 2):
        edges = [(u, v) for u in range(n) for v in range(n, 3*n)]
        for p in (Q(1, 3), Q(3, 4)):
            disconnected = Q(0)
            for retained in itertools.product((False, True), repeat=len(edges)):
                opened = sum(retained)
                if len(blocks(3*n, edges, retained)) > 1:
                    disconnected += p**opened * (1-p)**(len(edges)-opened)
                cases += 1
            bound = sum(comb(3*n, j)*(1-p)**((n*j+3)//4)
                        for j in range(1, 3*n//2+1))
            assert disconnected <= bound
    return cases


def main():
    counts, bipartite_cuts = layer_cut_checks()
    print(json.dumps({
        'status': 'passed',
        'sprinkling_configurations': sprinkling_checks(),
        'palm_partitions': palm_checks(),
        'layer_cut_count_vectors': counts,
        'bipartite_cut_count_vectors': bipartite_cuts,
        'finite_disconnection_configurations': finite_disconnection_checks(),
        'scope': 'Exact finite identities only; not verification of the infinite percolation theorems.',
    }, indent=2))


if __name__ == '__main__':
    main()
