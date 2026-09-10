#!/usr/bin/env python3
"""Exact finite contraction/gap checks for quotient-environment-gap.md; MSI only."""

import itertools
import json
from fractions import Fraction as Q

def partitions(n):
    """Generate each partition once without enumerating n**n label strings."""
    def extend(blocks, v):
        if v == n:
            yield tuple(frozenset(block) for block in blocks)
            return
        for i in range(len(blocks)):
            yield from extend(blocks[:i]+[blocks[i]+[v]]+blocks[i+1:], v+1)
        yield from extend(blocks+[[v]], v+1)
    yield from extend([], 0)


def is_psd(matrix):
    """Exact symmetric Schur complements, including singular zero pivots."""
    a = [list(row) for row in matrix]
    assert all(a[i][j] == a[j][i] for i in range(len(a)) for j in range(len(a)))
    while a:
        pivot = a[0][0]
        if pivot < 0:
            return False
        if pivot == 0:
            if any(a[0][j] for j in range(1, len(a))):
                return False
            a = [row[1:] for row in a[1:]]
        else:
            a = [[a[i][j]-a[i][0]*a[0][j]/pivot
                  for j in range(1, len(a))] for i in range(1, len(a))]
    return True


def connected(block, edges):
    reached = {next(iter(block))}
    while True:
        expanded = reached | {v for u, v in edges if u in reached and v in block}
        expanded |= {u for u, v in edges if v in reached and u in block}
        if expanded == reached:
            return reached == set(block)
        reached = expanded


def check_graph(name, n, edges, gap):
    degrees = [sum(v in edge for edge in edges) for v in range(n)]
    assert len(set(degrees)) == 1
    d = degrees[0]
    adjacency = [[int((min(i, j), max(i, j)) in edges) for j in range(n)]
                 for i in range(n)]
    original = [[Q(d if i == j else -adjacency[i][j])-gap*d*(Q(i == j)-Q(1, n))
                 for j in range(n)] for i in range(n)]
    assert is_psd(original)
    # The supplied gaps are sharp for these graphs, so a larger gap must fail.
    too_large = [[original[i][j]-Q(d, 100)*(Q(i == j)-Q(1, n))
                  for j in range(n)] for i in range(n)]
    assert not is_psd(too_large)
    count = 0
    for partition in partitions(n):
        k = len(partition)
        if k == 1 or not all(connected(block, edges) for block in partition):
            continue
        cell = {v: i for i, block in enumerate(partition) for v in block}
        masses = list(map(len, partition))
        a = [[0 for _ in range(k)] for _ in range(k)]
        for u, v in edges:
            i, j = cell[u], cell[v]
            if i != j:
                a[i][j] += 1
                a[j][i] += 1
        boundary = list(map(sum, a))
        total = sum(boundary)
        z = Q(total, n)
        assert all(0 < b <= d*m for b, m in zip(boundary, masses))
        nu = [Q(b, total) for b in boundary]
        # Full quadratic inequality, not only selected test vectors.
        comparison = [[Q(boundary[i] if i == j else -a[i][j])
                       -gap*(Q(boundary[i] if i == j else 0)
                             -Q(boundary[i]*boundary[j], total))
                       for j in range(k)] for i in range(k)]
        assert is_psd(comparison), (name, partition)
        # Independent original-edge and quotient-transition calculations.
        for phi in ([Q(i*i+2*i-1) for i in range(k)],
                    [Q((-1)**i, i+1) for i in range(k)]):
            lifted = [phi[cell[v]] for v in range(n)]
            mean_p = sum(lifted)/n
            var_p = sum((f-mean_p)**2 for f in lifted)/n
            mean_nu = sum(w*f for w, f in zip(nu, phi))
            var_nu = sum(w*(f-mean_nu)**2 for w, f in zip(nu, phi))
            density_mean = sum(Q(boundary[cell[v]], masses[cell[v]])*lifted[v]
                               for v in range(n))/n/z
            assert density_mean == mean_nu
            quotient_energy = sum(nu[i]*Q(a[i][j], boundary[i])*(phi[i]-phi[j])**2
                                  for i in range(k) for j in range(k))/2
            original_energy = sum((lifted[u]-lifted[v])**2 for u, v in edges)/n/d
            assert quotient_energy == Q(d)/z*original_energy
            assert var_nu <= Q(d)/z*var_p
            assert quotient_energy >= gap*var_nu
        count += 1
    return {"graph": name, "partitions": count, "original_gap": str(gap)}


def main():
    # Exercise negative and singular-pivot cases of the exact PSD verifier.
    assert is_psd([[Q(1), Q(1)], [Q(1), Q(1)]])
    assert is_psd([[Q(0), Q(0)], [Q(0), Q(1)]])
    assert not is_psd([[Q(0), Q(1)], [Q(1), Q(1)]])
    assert not is_psd([[Q(-1)]])
    graphs = [
        ("four_cycle", 4, [(0, 1), (0, 3), (1, 2), (2, 3)], Q(1)),
        ("complete_four", 4, list(itertools.combinations(range(4), 2)), Q(4, 3)),
        ("complete_bipartite_three_three", 6,
         [(i, j) for i in range(3) for j in range(3, 6)], Q(1)),
        ("three_cube", 8,
         [(i, j) for i, j in itertools.combinations(range(8), 2)
          if (i ^ j) in (1, 2, 4)], Q(2, 3)),
    ]
    results = [check_graph(*graph) for graph in graphs]
    print(json.dumps({"status": "passed", "arithmetic": "exact rational",
                      "scope": "Finite normalization and contraction gap checks; not an infinite proof",
                      "graphs": results,
                      "total_partitions": sum(r["partitions"] for r in results)}, indent=2))


if __name__ == '__main__':
    main()
