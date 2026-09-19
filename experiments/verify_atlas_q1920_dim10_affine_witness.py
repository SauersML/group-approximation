#!/usr/bin/env python3
"""Standalone exact audit of the Q1920 dimension-10 affine witness."""

from __future__ import annotations

from collections import deque
import json


P = 3


def matrix(rows):
    result = tuple(tuple(entry % P for entry in row) for row in rows)
    assert result and all(len(row) == len(result) for row in result)
    return result


def identity(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def multiply(left, right):
    n = len(left)
    assert len(right) == n
    return tuple(
        tuple(sum(left[i][k] * right[k][j] for k in range(n)) % P
              for j in range(n))
        for i in range(n)
    )


def power(value, exponent):
    result = identity(len(value))
    factor = value
    while exponent:
        if exponent & 1:
            result = multiply(result, factor)
        factor = multiply(factor, factor)
        exponent >>= 1
    return result


def inverse(value):
    n = len(value)
    rows = [list(value[i]) + list(identity(n)[i]) for i in range(n)]
    for column in range(n):
        pivot = next(row for row in range(column, n)
                     if rows[row][column] % P)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scalar = pow(rows[column][column], -1, P)
        rows[column] = [(scalar * entry) % P for entry in rows[column]]
        for row in range(n):
            if row == column:
                continue
            scalar = rows[row][column]
            if scalar:
                rows[row] = [
                    (entry - scalar * pivot_entry) % P
                    for entry, pivot_entry in zip(rows[row], rows[column])
                ]
    return tuple(tuple(row[n:]) for row in rows)


def product(*values):
    result = identity(len(values[0]))
    for value in values:
        result = multiply(result, value)
    return result


def homogeneous_linear(value):
    n = len(value)
    return tuple(tuple(value[i][j] if i < n and j < n else int(i == j)
                       for j in range(n + 1))
                 for i in range(n + 1))


def homogeneous_translation(vector):
    n = len(vector)
    return tuple(
        tuple(
            int(i == j) if i < n else (vector[j] if j < n else 1)
            for j in range(n + 1)
        )
        for i in range(n + 1)
    )


def encode_row(row):
    code = 0
    place = 1
    for entry in row:
        code += entry * place
        place *= P
    return code


def add_row_codes(left, right, n):
    result = 0
    place = 1
    for _ in range(n):
        left, a = divmod(left, P)
        right, b = divmod(right, P)
        result += ((a + b) % P) * place
        place *= P
    return result


def right_row_table(value):
    """Map each encoded row v to encoded v*value."""
    n = len(value)
    table = [0]
    for row in value:
        image = encode_row(row)
        twice = add_row_codes(image, image, n)
        old = table
        table = (
            old
            + [add_row_codes(item, image, n) for item in old]
            + [add_row_codes(item, twice, n) for item in old]
        )
    assert len(table) == P**n
    return table


def linear_group_order(generators, expected):
    n = len(generators[0])
    tables = [right_row_table(generator) for generator in generators]
    start = tuple(P**i for i in range(n))
    seen = {start}
    queue = deque([start])
    while queue:
        current = queue.popleft()
        for table in tables:
            successor = tuple(table[row] for row in current)
            if successor not in seen:
                seen.add(successor)
                assert len(seen) <= expected, "group exceeded expected order"
                queue.append(successor)
    assert len(seen) == expected
    return len(seen)


def affine_group_order(generators, expected, table_cache):
    """Enumerate pairs (A,v) with product (A,v)(B,w)=(AB,vB+w)."""
    n = len(generators[0][0])
    prepared = []
    for linear, translation in generators:
        table = table_cache.setdefault(linear, right_row_table(linear))
        prepared.append((table, encode_row(translation)))
    start = tuple(P**i for i in range(n)) + (0,)
    seen = {start}
    queue = deque([start])
    while queue:
        current = queue.popleft()
        for table, shift in prepared:
            successor = (
                tuple(table[row] for row in current[:-1])
                + (add_row_codes(table[current[-1]], shift, n),)
            )
            if successor not in seen:
                seen.add(successor)
                assert len(seen) <= expected, "group exceeded expected order"
                queue.append(successor)
    assert len(seen) == expected
    return len(seen)


def row_times_matrix(row, value):
    n = len(row)
    return tuple(sum(row[k] * value[k][j] for k in range(n)) % P
                 for j in range(n))


def rank(rows):
    if not rows:
        return 0
    work = [list(row) for row in rows]
    row = 0
    for column in range(len(work[0])):
        pivot = next((i for i in range(row, len(work)) if work[i][column]), None)
        if pivot is None:
            continue
        work[row], work[pivot] = work[pivot], work[row]
        scalar = pow(work[row][column], -1, P)
        work[row] = [(scalar * entry) % P for entry in work[row]]
        for i in range(len(work)):
            if i != row and work[i][column]:
                scalar = work[i][column]
                work[i] = [(a - scalar * b) % P
                           for a, b in zip(work[i], work[row])]
        row += 1
        if row == len(work):
            break
    return row


def fixed_space_dimension(generators):
    n = len(generators[0])
    constraints = []
    one = identity(n)
    for generator in generators:
        for column in range(n):
            constraints.append(tuple(
                (generator[row][column] - one[row][column]) % P
                for row in range(n)
            ))
    return n - rank(constraints)


def centralizer_dimension(generators):
    n = len(generators[0])
    constraints = []
    for generator in generators:
        for i in range(n):
            for j in range(n):
                equation = [0] * (n * n)
                for k in range(n):
                    equation[i * n + k] += generator[k][j]
                    equation[k * n + j] -= generator[i][k]
                constraints.append(tuple(entry % P for entry in equation))
    return n * n - rank(constraints)


def matrix_algebra_dimension(generators):
    """Dimension of the F3-algebra generated by the matrices."""
    n = len(generators[0])
    echelon = {}

    def adjoin(value):
        vector = [entry for row in value for entry in row]
        for pivot in sorted(echelon):
            if vector[pivot]:
                scalar = vector[pivot]
                vector = [(a - scalar * b) % P
                          for a, b in zip(vector, echelon[pivot])]
        pivot = next((i for i, entry in enumerate(vector) if entry), None)
        if pivot is None:
            return False
        scalar = pow(vector[pivot], -1, P)
        vector = [(scalar * entry) % P for entry in vector]
        for old_pivot, old in list(echelon.items()):
            if old[pivot]:
                scalar = old[pivot]
                echelon[old_pivot] = [
                    (a - scalar * b) % P for a, b in zip(old, vector)
                ]
        echelon[pivot] = vector
        return True

    start = identity(n)
    assert adjoin(start)
    queue = deque([start])
    while queue:
        value = queue.popleft()
        for generator in generators:
            successor = multiply(value, generator)
            if adjoin(successor):
                queue.append(successor)
    return len(echelon)


def translation_span_rank(seed, generators):
    vectors = [seed]
    current_rank = rank(vectors)
    index = 0
    while index < len(vectors) and current_rank < len(seed):
        vector = vectors[index]
        index += 1
        for generator in generators:
            image = row_times_matrix(vector, generator)
            new_rank = rank(vectors + [image])
            if new_rank > current_rank:
                vectors.append(image)
                current_rank = new_rank
                if current_rank == len(seed):
                    break
    return current_rank, vectors


r0 = matrix([
    [0, 0, 0, 1, 0, 0, 0, 2, 2, 0],
    [0, 2, 0, 0, 1, 2, 0, 1, 2, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    [2, 0, 0, 2, 0, 1, 0, 0, 2, 0],
    [0, 1, 0, 0, 0, 1, 2, 0, 1, 2],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 2],
    [1, 0, 0, 1, 0, 0, 0, 0, 2, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
])
u0 = matrix([
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    [0, 0, 0, 0, 0, 1, 0, 0, 2, 0],
    [0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 2],
    [0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
])
t0 = matrix([
    [0, 0, 0, 0, 1, 2, 0, 1, 2, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 2, 0, 0, 0, 0, 1, 0],
    [1, 0, 0, 1, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    [2, 0, 2, 2, 0, 0, 0, 0, 1, 0],
    [0, 1, 0, 0, 0, 1, 1, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
    [1, 0, 0, 1, 0, 0, 0, 0, 2, 0],
    [0, 2, 0, 0, 0, 2, 0, 0, 2, 0],
])
s0 = matrix([
    [0, 0, 2, 0, 0, 0, 0, 0, 2, 0],
    [0, 0, 0, 0, 2, 0, 0, 2, 0, 1],
    [2, 0, 0, 2, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 1, 1, 0],
    [0, 0, 0, 2, 1, 0, 0, 1, 1, 0],
    [0, 2, 0, 0, 0, 2, 2, 0, 2, 2],
    [0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 2, 0],
    [0, 1, 0, 0, 0, 1, 0, 0, 1, 0],
])
c0 = matrix([
    [2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 2, 0, 0, 0, 0, 2, 0],
    [0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 2, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
])
z0 = (1, 1, 0, 2, 1, 2, 0, 2, 0, 0)


def main():
    d = 10
    zero = (0,) * d
    one10 = identity(d)
    r = homogeneous_linear(r0)
    u = homogeneous_linear(u0)
    t = homogeneous_linear(t0)
    s = homogeneous_linear(s0)
    c = homogeneous_linear(c0)
    z = homogeneous_translation(z0)
    y = inverse(t)
    b = multiply(s, t)
    one = identity(d + 1)

    relations = {
        "r^3": power(r, 3),
        "y^3": power(y, 3),
        "u^2": power(u, 2),
        "b^2": power(b, 2),
        "u*r*u*r": product(u, r, u, r),
        "b*y*b*y": product(b, y, b, y),
        "(r^-1*b)^3": power(product(inverse(r), b), 3),
        "(u*y)^3": power(product(u, y), 3),
        "(u*r*y^-1)^3": power(product(u, r, inverse(y)), 3),
        "(r*b*y)^3": power(product(r, b, y), 3),
        "z^3": power(z, 3),
        "c^2": power(c, 2),
        "[r,z]": product(r, z, inverse(r), inverse(z)),
        "[c,r]": product(c, r, inverse(c), inverse(r)),
        "(c*z)^2": power(product(c, z), 2),
        "[u,z]": product(u, z, inverse(u), inverse(z)),
        "[u,c]": product(u, c, inverse(u), inverse(c)),
        "(c*t)^3": power(product(c, t), 3),
        "q19243": product(t, c, s, c, inverse(t), c, s, t, c),
    }
    failures = [name for name, value in relations.items() if value != one]
    assert not failures, failures
    assert c != one and z != one
    omitted = power(product(z, b), 3)
    assert omitted != one

    y0 = inverse(t0)
    b0 = multiply(s0, t0)
    assert y == homogeneous_linear(y0)
    assert b == homogeneous_linear(b0)
    q_order = linear_group_order([r0, y0, u0, b0], 1920)
    linear_order = linear_group_order([r0, y0, u0, b0, c0], 30720)
    q_algebra_dimension = matrix_algebra_dimension([r0, y0, u0, b0])
    assert q_algebra_dimension == d * d
    a_fixed_dimension = fixed_space_dimension([r0, u0])
    a_centralizer_dimension = centralizer_dimension([r0, u0])
    assert a_fixed_dimension == 3
    assert a_centralizer_dimension == 19
    assert row_times_matrix(z0, r0) == z0
    assert row_times_matrix(z0, u0) == z0
    assert row_times_matrix(z0, c0) == tuple((-entry) % P for entry in z0)

    table_cache = {}
    f_order = affine_group_order(
        [(r0, zero), (one10, z0), (c0, zero), (u0, zero)],
        36,
        table_cache,
    )
    j_order = affine_group_order(
        [(t0, zero), (s0, zero), (c0, zero)],
        24,
        table_cache,
    )
    forward_order = affine_group_order(
        [(r0, zero), (one10, z0), (b0, zero)],
        324,
        table_cache,
    )
    span_rank, spanning_vectors = translation_span_rank(
        z0, [r0, y0, u0, b0, c0]
    )
    assert span_rank == d
    affine_order = P**span_rank * linear_order
    assert affine_order == 1_813_985_280

    print(json.dumps({
        "field": P,
        "linear_dimension": d,
        "homogeneous_dimension": d + 1,
        "relations_checked": sorted(relations),
        "all_reduced_seam_relators": True,
        "protected_nonidentity": {"c": True, "z": True},
        "orders": {
            "Q=<r,y,u,b>": q_order,
            "F=<r,z,c,u>": f_order,
            "J=<t,s,c>": j_order,
            "forward=<r,z,b>": forward_order,
            "linear=<r,y,u,b,c>": linear_order,
            "affine=<r,y,u,b,c,z>": affine_order,
        },
        "translation_orbit_span_rank": span_rank,
        "Q_matrix_algebra_dimension": q_algebra_dimension,
        "A_fixed_dimension": a_fixed_dimension,
        "End_A_dimension": a_centralizer_dimension,
        "translation_spanning_vectors": spanning_vectors,
        "omitted_full_packet_relator_(z*b)^3_is_identity": False,
        "status": "ok",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
