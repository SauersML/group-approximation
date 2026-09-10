#!/usr/bin/env python3
"""Exact finite product-noise/projection checks. Execute on MSI only."""

import itertools
import json
from fractions import Fraction as F

from replay_critical_quotient import blocks
from replay_quotient_environment_gap import is_psd


def zero(n):
    return [[F(0) for _ in range(n)] for _ in range(n)]


def identity(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def add(a, b, scale=F(1)):
    return [[x+scale*y for x, y in zip(row, other)] for row, other in zip(a, b)]


def multiply(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(a)))
             for j in range(len(a))] for i in range(len(a))]


def inverse(a):
    n = len(a)
    aug = [row+other for row, other in zip(a, identity(n))]
    for i in range(n):
        pivot = next(k for k in range(i, n) if aug[k][i])
        aug[i], aug[pivot] = aug[pivot], aug[i]
        scale = aug[i][i]
        aug[i] = [v/scale for v in aug[i]]
        for j in range(n):
            if j != i:
                scale = aug[j][i]
                aug[j] = [v-scale*w for v, w in zip(aug[j], aug[i])]
    result = [row[n:] for row in aug]
    assert multiply(a, result) == identity(n)
    return result


def projection(n, partition, ghosts=()):
    result = zero(n)
    for cell in partition:
        if any(v in cell for v in ghosts):
            continue
        for i in cell:
            for j in cell:
                result[i][j] = F(1, len(cell))
    return result


def laplacian(n, edges):
    result = zero(n)
    for i, j in edges:
        result[i][i] += 1
        result[j][j] += 1
        result[i][j] -= 1
        result[j][i] -= 1
    return result


def ordinary_checks(n, edges, p):
    m = len(edges)
    masks = list(itertools.product((0, 1), repeat=m))
    values = {bits: projection(n, blocks(n, edges, bits)) for bits in masks}
    weights = {bits: p**sum(bits)*(1-p)**(m-sum(bits)) for bits in masks}
    q, derivative, energy = zero(n), zero(n), zero(n)
    for bits in masks:
        q = add(q, values[bits], weights[bits])
        score = sum(bits)/p-(m-sum(bits))/(1-p)
        derivative = add(derivative, values[bits], weights[bits]*score)
    for e in range(m):
        for bits in masks:
            if bits[e]:
                continue
            opened = bits[:e]+(1,)+bits[e+1:]
            delta = add(values[bits], values[opened], F(-1))
            assert multiply(delta, delta) == delta
            other_weight = weights[bits]/(1-p)
            energy = add(energy, multiply(delta, delta), p*(1-p)*other_weight)
    assert energy == add(zero(n), derivative, -p*(1-p))
    variance = add(q, multiply(q, q), F(-1))
    deficit = add(energy, variance, F(-1))
    assert is_psd(deficit)
    # Use unnormalized centered coordinates to keep every coefficient rational.
    noise_deficit = zero(n)
    for subset in masks:
        size = sum(subset)
        if size < 2:
            continue
        coefficient = zero(n)
        norm_squared = (p*(1-p))**size
        for bits in masks:
            character = F(1)
            for e, selected in enumerate(subset):
                if selected:
                    character *= bits[e]-p
            coefficient = add(coefficient, values[bits], weights[bits]*character/norm_squared)
        noise_deficit = add(noise_deficit, multiply(coefficient, coefficient),
                            (size-1)*norm_squared)
    assert noise_deficit == deficit
    target = add(identity(n), laplacian(n, edges), p/(2*(1-p)))
    assert is_psd(add(inverse(q), target, F(-1)))
    assert is_psd(add(inverse(target), q, F(-1)))
    return len(masks), sum(sum(s) >= 2 for s in masks)


def ghost_checks():
    count = 0
    for n, edges in [(2, [(0, 1)]), (3, [(0, 1), (1, 2), (0, 2)])]:
        for p, s in [(F(1, 2), F(1, 4)), (F(1, 3), F(2, 5))]:
            q = zero(n)
            for bits in itertools.product((0, 1), repeat=len(edges)):
                partition = blocks(n, edges, bits)
                edge_weight = p**sum(bits)*(1-p)**(len(edges)-sum(bits))
                for marks in itertools.product((0, 1), repeat=n):
                    ghosts = [i for i, mark in enumerate(marks) if mark]
                    weight = edge_weight*s**sum(marks)*(1-s)**(n-sum(marks))
                    q = add(q, projection(n, partition, ghosts), weight)
                    count += 1
            target = add(add(identity(n), laplacian(n, edges), p/(2*(1-p))),
                         identity(n), s/(1-s))
            assert is_psd(add(inverse(target), q, F(-1)))
            if n == 2 and p == F(1, 2):
                q0 = [[F(3, 4), F(1, 4)], [F(1, 4), F(3, 4)]]
                qloss = add(q0, q, F(-1))
                rloss = add(q0, inverse(target), F(-1))
                # A concrete failure of subtracting two separate order bounds.
                assert qloss[0][0] == F(15, 64)
                assert rloss[0][0] == F(9, 56)
                assert not is_psd(add(rloss, qloss, F(-1)))
    return count


def main():
    configurations = 0
    noise_coefficients = 0
    graph_parameters = 0
    graphs = [(2, [(0, 1)]), (4, [(0, 1), (1, 2), (2, 3)]),
              (4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
              (4, list(itertools.combinations(range(4), 2))),
              (5, [(i, j) for i in range(2) for j in range(2, 5)])]
    for n, edges in graphs:
        for p in (F(1, 5), F(1, 2), F(4, 5)):
            c, w = ordinary_checks(n, edges, p)
            configurations += c
            noise_coefficients += w
            graph_parameters += 1
    print(json.dumps({"status": "passed", "arithmetic": "exact rational",
                      "scope": "Finite identities and PSD checks, not an infinite proof",
                      "graph_parameter_pairs": graph_parameters,
                      "edge_configurations": configurations,
                      "higher_noise_coefficients": noise_coefficients,
                      "edge_ghost_configurations": ghost_checks(),
                      "invalid_subtraction_diagonal": {"actual": "15/64", "claimed_upper": "9/56"}},
                     indent=2))


if __name__ == '__main__':
    main()
