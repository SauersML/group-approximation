#!/usr/bin/env python3
"""Finite checks for the local torsion sparsifier proof.

No infinite Burnside group, invariant measure theorem, or conjecture is
verified here. The Heisenberg group is a finite test fixture, not an example
of the infinite hypotheses.
"""
from __future__ import annotations
import argparse
import itertools
import json
from collections import deque
from fractions import Fraction
from pathlib import Path
from math import gcd


def mul(g: tuple[int, int, int], h: tuple[int, int, int], p: int = 3):
    x, y, z = g
    u, v, w = h
    return ((x + u) % p, (y + v) % p, (z + w + x * v) % p)


def power(g, k: int, p: int = 3):
    h = (0, 0, 0)
    for _ in range(k):
        h = mul(h, g, p)
    return h


def edge(x, y):
    return tuple(sorted((x, y)))


def cycle_checks():
    cases = 0
    for n in (3, 5, 7, 9, 11):
        for mask in range(1 << n):
            boundary = [bool((mask >> i & 1) != (mask >> ((i + 1) % n) & 1)) for i in range(n)]
            old = sum(boundary)
            for deleted in range(n):
                new = old - boundary[deleted]
                assert 2 * new >= old
                cases += 1
    return {"cycle_lengths": [3, 5, 7, 9, 11], "cut_deletion_pairs": cases}


def density_checks():
    cases = 0
    probabilities = []
    for lengths in ((2,), (2, 2), (2, 2, 2), (2, 2, 2, 2), (2, 3), (2, 3, 4)):
        coords = 1 + sum(lengths)
        intervals = []
        start = 1
        for size in lengths:
            intervals.append(range(start, start + size))
            start += size
        for q in (Fraction(1, 5), Fraction(1, 3), Fraction(1, 2)):
            total = Fraction(0)
            for mask in range(1 << coords):
                selected = bool(mask & 1)
                success = any(all(mask >> j & 1 for j in block) for block in intervals)
                retained = selected or not success
                ones = mask.bit_count()
                if retained:
                    total += q ** ones * (1 - q) ** (coords - ones)
            formula = q + (1 - q) * product(1 - q ** length for length in lengths)
            assert total == formula
            probabilities.append({"lengths": list(lengths), "q": str(q), "retention": str(total)})
            cases += 1
    return {"independent_probability_identities": cases, "examples": probabilities}


def product(xs):
    value = Fraction(1)
    for x in xs:
        value *= x
    return value


def bfs(adj, x):
    dist = {x: 0}
    queue = deque([x])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                queue.append(v)
    return dist


def fixture_checks():
    p = 3
    vertices = list(itertools.product(range(p), repeat=3))
    identity = (0, 0, 0)
    a, b, z = (1, 0, 0), (0, 1, 0), (0, 0, 1)
    assert all(power(x, p) == identity for x in vertices)
    # Four elements of H=<b,z> and their explicit positive words.
    words = [(b,), (z,), (b, z), (b, b, z)]
    bs = []
    for word in words:
        value = identity
        for letter in word:
            value = mul(value, letter)
        bs.append(value)
    cs = [mul(a, x) for x in bs]
    sets = [{power(c, i) for i in range(1, p)} for c in cs]
    assert len(set.union(*sets)) == sum(map(len, sets))
    assert identity not in set.union(*sets)
    support = [identity] + sorted(set.union(*sets))

    # Cyclic backbone: remove one positive edge from every b- and z-cycle.
    backbone = set()
    cycle_of = {}
    for generator in (b, z):
        seen = set()
        for x in vertices:
            if x in seen:
                continue
            orbit = [mul(x, power(generator, i)) for i in range(p)]
            seen.update(orbit)
            deleted_source = min(orbit)
            for v in orbit:
                cycle_of[(generator, v)] = deleted_source
                if v != deleted_source:
                    backbone.add(edge(v, mul(v, generator)))
    assert len(backbone) == 2 * len(vertices) * (p - 1) // p

    def append_backbone_step(path, generator):
        v = path[-1]
        endpoint = mul(v, generator)
        if edge(v, endpoint) in backbone:
            path.append(endpoint)
        else:
            inverse = power(generator, p - 1)
            for _ in range(p - 1):
                path.append(mul(path[-1], inverse))
            assert path[-1] == endpoint

    max_word_length = max(map(len, words))
    proven_bound = (p - 1) * (p * max_word_length + 1)
    mask_cases = route_cases = shortest_path_cases = 0
    max_prescribed = max_shortest = 0
    witness_cases = 0
    for mask in range(1 << len(support)):
        A = {support[j] for j in range(len(support)) if mask >> j & 1}
        successful = {}
        for x in vertices:
            successful[x] = [i for i, c in enumerate(cs) if all(mul(x, power(c, ell)) in A for ell in range(1, p))]
        retained_sources = {x for x in vertices if x in A or not successful[x]}
        graph = set(backbone)
        graph.update(edge(x, mul(x, a)) for x in retained_sources)
        adj = {x: set() for x in vertices}
        for x, y in graph:
            adj[x].add(y)
            adj[y].add(x)
        assert len(bfs(adj, identity)) == len(vertices)
        for x in vertices:
            xa = mul(x, a)
            if x in retained_sources:
                path = [xa, x]
            else:
                i = successful[x][0]
                c = cs[i]
                path = [xa]
                for ell in range(1, p + 1):
                    for letter in words[i]:
                        append_backbone_step(path, letter)
                    assert path[-1] == mul(x, power(c, ell))
                    if ell < p:
                        assert path[-1] in A
                        path.append(mul(path[-1], a))
                assert path[-1] == x
            assert all(edge(u, v) in graph for u, v in zip(path, path[1:]))
            assert len(path) - 1 <= proven_bound
            route_cases += 1
            max_prescribed = max(max_prescribed, len(path) - 1)
            distances = bfs(adj, x)
            for generator in (a, b, z):
                y = mul(x, generator)
                assert distances[y] <= proven_bound
                max_shortest = max(max_shortest, distances[y])
                shortest_path_cases += 1
            # The first non-backbone edge on any x--xa path witnesses the
            # deterministic support-ball argument used in the lower bound.
            R = distances[xa]
            ambient_adj = {v: {mul(v, g) for g in (a, power(a, 2), b, power(b, 2), z, power(z, 2))} for v in vertices}
            ball = {v for v, dist in bfs(ambient_adj, x).items() if dist <= R}
            assert any(u in ball and v in ball for u, v in graph - backbone)
            witness_cases += 1
        mask_cases += 1
    return {
        "fixture": "Heisenberg group over F_3; finite fixture only",
        "group_order": len(vertices),
        "detour_count": len(cs),
        "support_coordinates_varied": len(support),
        "all_other_selector_coordinates": 0,
        "selector_masks": mask_cases,
        "prescribed_routes": route_cases,
        "ambient_generator_shortest_paths": shortest_path_cases,
        "local_sparse_edge_witnesses": witness_cases,
        "proven_route_bound_in_fixture": proven_bound,
        "maximum_prescribed_length_observed": max_prescribed,
        "maximum_generator_shortest_distance_observed": max_shortest,
    }


def ball_checks():
    count = 0
    for degree in range(3, 13):
        for radius in range(0, 16):
            formula = 1 + degree * ((degree - 1) ** radius - 1) // (degree - 2)
            direct = 1 + sum(degree * (degree - 1) ** j for j in range(radius))
            assert formula == direct
            count += 1
    return {"ball_volume_identities": count}


def prime_divisor_checks():
    count = 0
    examples = []
    for n in range(3, 2002, 2):
        p = next(d for d in range(3, n + 1, 2) if n % d == 0)
        assert all(p % d for d in range(2, p))
        ell = n // p
        order = n // gcd(n, ell)
        assert order == p
        old = 2 - Fraction(2, n)
        new = 2 - Fraction(2, p)
        assert 1 < new <= old
        assert (new < old) == (p < n)
        if n % 3 == 0:
            assert new == Fraction(4, 3)
        # Abelianization separates the nonidentity power elements' coordinates.
        assert (ell % n, 0) != (0, ell % n)
        assert (ell * (p - 1)) % n != 0 and (ell * p) % n == 0
        count += 1
        if n in (1003, 1005, 1015, 1029):
            examples.append({'n': n, 'least_prime_divisor': p,
                             'power': ell, 'old_upper_bound': str(old),
                             'new_upper_bound': str(new)})
    return {'odd_exponents_tested': count,
            'scope': 'Finite cyclic order and rational cost arithmetic only',
            'examples': examples}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('local-sparsifier-checks.json'))
    args = parser.parse_args()
    result = {
        "status": "PASS",
        "scope": "Exact finite combinatorics and rational identities only; not a proof assistant or an infinite-group verification.",
        "cycle_boundary": cycle_checks(),
        "selector_density": density_checks(),
        "finite_group_routing": fixture_checks(),
        "ball_volume": ball_checks(),
        "prime_divisor_arithmetic": prime_divisor_checks(),
        "unverified_by_this_script": [
            "Burnside algebra and nonamenability",
            "Abért--Weiss finite-pattern approximation",
            "infinite invariant construction and cost infima",
            "mathematical novelty",
            "either universal conjecture"
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'selector_density'}, indent=2))


if __name__ == '__main__':
    main()
