#!/usr/bin/env python3
"""Exact action and matrix checks for the nonlinear rectangular F_2 section."""

import itertools
import json
import random


E, S, T = (), (1,), (2,)


def mul(a, b):
    out = list(a)
    for letter in b:
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def inv(g):
    return tuple(-letter for letter in reversed(g))


def prod(a, b):
    return {mul(x, y) for x in a for y in b}


def ball(radius):
    out = {E}
    for _ in range(radius):
        out |= prod(out, {S, inv(S), T, inv(T)})
    return out


N, M = {E, S, T}, {E, inv(T)}
LEFT, RIGHT = mul(T, S), mul(T, inv(S))


def tau(x):
    out = {}
    for g in prod(set(x), {inv(n) for n in N}):
        value = (x.get(mul(g, T), 0), x.get(g, 0) & x.get(mul(g, S), 0))
        if value != (0, 0):
            out[g] = value
    return out


def sigma(y):
    return {mul(g, T): value[0] for g, value in y.items() if value[0]}


def flip_output(y, track):
    out = dict(y)
    value = list(y.get(E, (0, 0)))
    value[track] ^= 1
    if value == [0, 0]:
        out.pop(E, None)
    else:
        out[E] = tuple(value)
    return out


def compress_flip(x, track):
    y = flip_output(tau(x), track)
    candidate = sigma(y)
    # V* kills a basis vector outside the image; sigma gives the only
    # possible input when that basis vector is in the image.
    return candidate if tau(candidate) == y else None


def mmul(a, b):
    return [[sum(x * y for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def main():
    sites = (T, LEFT, RIGHT)
    assert len(set(sites)) == 3
    locality_set = prod(prod({inv(m) for m in M}, {inv(n) for n in N}), N)
    assert set(sites) <= locality_set
    assert prod(M, N) != prod(N, M)
    patterns = list(itertools.product((0, 1), repeat=3))
    rng = random.Random(20260908)
    outside = sorted(ball(2) - set(sites))
    action_checks = 0
    killed_second_track_checks = 0
    matrices = []
    for context_index in range(16):
        context = {} if context_index == 0 else {
            g: 1 for g in outside if rng.randrange(2)
        }
        matrix = [[0 for _ in patterns] for _ in patterns]
        for col, bits in enumerate(patterns):
            x = dict(context)
            x.update({g: bit for g, bit in zip(sites, bits) if bit})
            assert sigma(tau(x)) == x
            actual = compress_flip(x, 0)
            if bits[1] or bits[2]:
                assert actual is None
            else:
                expected = dict(x)
                if bits[0]:
                    expected.pop(T)
                else:
                    expected[T] = 1
                assert actual == expected
                row = patterns.index(tuple(actual.get(g, 0) for g in sites))
                matrix[row][col] = 1
            assert compress_flip(x, 1) is None
            killed_second_track_checks += 1
            action_checks += 1
        matrices.append(matrix)
    assert all(matrix == matrices[0] for matrix in matrices)
    matrix = matrices[0]
    assert matrix == [list(row) for row in zip(*matrix)]
    square = mmul(matrix, matrix)
    expected_square = [[int(i == j and not patterns[i][1] and not patterns[i][2])
                        for j in range(8)] for i in range(8)]
    assert square == expected_square
    defect = [[int(i == j) - square[i][j] for j in range(8)] for i in range(8)]
    assert mmul(defect, defect) == defect
    diagonal = [defect[i][i] for i in range(8)]
    assert set(diagonal) == {0, 1} and sum(diagonal) == 6
    result = {
        "status": "passed",
        "scope": "exact finite-support basis actions on the infinite free group F_2",
        "encoder": "tau(x)(g)=(x(gt),x(g) AND x(gs))",
        "decoder": "sigma(a,b)(g)=a(gt^-1)",
        "alphabet_sizes": {"encoder_input": 2, "encoder_output": 4},
        "basis_patterns": len(patterns),
        "outside_contexts": len(matrices),
        "split_and_first_track_compression_checks": action_checks,
        "zero_second_track_compression_checks": killed_second_track_checks,
        "uniform_locality_bound_size_at_identity": len(locality_set),
        "compression_matrix": matrix,
        "multiplicative_defect_diagonal": diagonal,
        "multiplicative_defect_is_nonzero_projection": True,
        "multiplicative_defect_norm": 1,
        "range_projection_distance": "1/2 by the infinite-group proof, not this finite replay",
        "general_conjecture_proved": False,
        "not_a_gottschalk_counterexample": True,
        "lean_verified": False,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
