"""Verify the fixed six-generator Hodge certificate with integer arithmetic.

This verifier uses only the Python standard library.  It neither imports the
discovery programs nor trusts floating-point positivity, stored residuals, or
a presentation-completeness theorem.  Its group is the concrete SL(3,Z).
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import itertools
import json
from pathlib import Path
import struct
import zipfile


IDENTITY = (1, 0, 0, 0, 1, 0, 0, 0, 1)
ROOTS = ((0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1))
SCALE = 10**16
EXPECTED_ROWS = (
    11670886519714,
    11659124680677,
    11665866556524,
    11658749718021,
    11658998556031,
    11658961981218,
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_int64_array(archive, name, shape):
    """Read precisely NPY v1.0, C-order, little-endian signed int64 data."""
    payload = archive.read(name + ".npy")
    require(payload[:8] == b"\x93NUMPY\x01\x00", name + ": wrong NPY format")
    require(len(payload) >= 10, name + ": truncated NPY header")
    header_size = struct.unpack("<H", payload[8:10])[0]
    body_start = 10 + header_size
    require(body_start <= len(payload), name + ": truncated NPY header")
    header = ast.literal_eval(payload[10:body_start].decode("ascii"))
    require(
        header == {"descr": "<i8", "fortran_order": False, "shape": shape},
        name + ": wrong dtype, shape, order, or header keys",
    )
    count = 1
    for dimension in shape:
        count *= dimension
    require(len(payload) == body_start + 8 * count, name + ": wrong payload size")
    return struct.unpack("<" + "q" * count, payload[body_start:])


def load_factor(path):
    shapes = {
        "factor_numerators": (102, 132),
        "group_support": (22, 9),
        "factor_denominator": (1,),
        "radius": (1,),
        "gap_numerator": (1,),
        "gap_denominator": (1,),
    }
    with zipfile.ZipFile(path) as archive:
        require(
            sorted(archive.namelist()) == sorted(name + ".npy" for name in shapes),
            "unexpected or duplicate NPZ members",
        )
        arrays = {
            name: read_int64_array(archive, name, shape)
            for name, shape in shapes.items()
        }
    require(arrays["factor_denominator"] == (10**8,), "wrong factor denominator")
    require(arrays["radius"] == (0,), "wrong support radius")
    require(arrays["gap_numerator"] == (1,), "wrong gap numerator")
    require(arrays["gap_denominator"] == (250,), "wrong gap denominator")
    flat = arrays["factor_numerators"]
    factor = tuple(flat[132 * row:132 * (row + 1)] for row in range(102))
    flat_support = arrays["group_support"]
    support = tuple(flat_support[9 * row:9 * (row + 1)] for row in range(22))
    return factor, support


def matmul(left, right):
    return tuple(
        sum(left[3 * row + k] * right[3 * k + column] for k in range(3))
        for row in range(3) for column in range(3)
    )


def inverse(matrix):
    a, b, c, d, e, f, g, h, i = matrix
    result = (
        e * i - f * h, c * h - b * i, b * f - c * e,
        f * g - d * i, a * i - c * g, c * d - a * f,
        d * h - e * g, b * g - a * h, a * e - b * d,
    )
    require(matmul(matrix, result) == IDENTITY, "group matrix is not in SL(3,Z)")
    require(matmul(result, matrix) == IDENTITY, "invalid matrix inverse")
    return result


def add_term(element, group, coefficient):
    value = element.get(group, 0) + coefficient
    if value:
        element[group] = value
    elif group in element:
        del element[group]


def add_into(target, source):
    for group, coefficient in source.items():
        add_term(target, group, coefficient)


def star(element):
    return {inverse(group): coefficient for group, coefficient in element.items()}


def product(left, right):
    result = {}
    for g, a in left.items():
        for h, b in right.items():
            add_term(result, matmul(g, h), a * b)
    return result


def literal_presentation():
    generators = []
    for row, column in ROOTS:
        matrix = list(IDENTITY)
        matrix[3 * row + column] = 1
        generators.append(tuple(matrix))
    index = {root: number for number, root in enumerate(ROOTS)}
    relators = []
    for i, j, k in itertools.permutations(range(3)):
        a, b, c = index[(i, j)], index[(j, k)], index[(i, k)]
        relators.append(((a, 1), (b, 1), (a, -1), (b, -1), (c, -1)))
    for left, right in itertools.combinations(ROOTS, 2):
        i, j = left
        k, ell = right
        if i != ell and j != k:
            a, b = index[left], index[right]
            relators.append(((a, 1), (b, 1), (a, -1), (b, -1)))
    relators.append(((0, 1), (2, -1), (0, 1)) * 4)
    require(len(relators) == 13, "wrong relator count")
    return tuple(generators), tuple(relators)


def fox_hodge(generators, relators):
    generator_inverses = tuple(inverse(g) for g in generators)
    d = tuple({g: 1, IDENTITY: -1} for g in generators)
    support = {IDENTITY, *generator_inverses}
    boundary = []
    for word in relators:
        row = [{} for _ in range(6)]
        prefix = IDENTITY
        for generator, sign in word:
            if sign == 1:
                add_term(row[generator], prefix, 1)
                support.add(prefix)
                prefix = matmul(prefix, generators[generator])
            else:
                prefix = matmul(prefix, generator_inverses[generator])
                add_term(row[generator], prefix, -1)
                support.add(prefix)
        require(prefix == IDENTITY, "a displayed relator is nonidentity")
        chain = {}
        for i in range(6):
            add_into(chain, product(row[i], d[i]))
        require(not chain, "Fox chain identity B D = 0 failed")
        boundary.append(row)

    delta = [[{} for _ in range(6)] for _ in range(6)]
    for i in range(6):
        for j in range(6):
            add_into(delta[i][j], product(d[i], star(d[j])))
            for row in boundary:
                add_into(delta[i][j], product(star(row[i]), row[j]))
    for i in range(6):
        for j in range(6):
            require(delta[i][j] == star(delta[j][i]), "Hodge matrix is not Hermitian")
    return delta, tuple(sorted(support))


def verify(path):
    factor, stored_support = load_factor(path)
    generators, relators = literal_presentation()
    delta, support = fox_hodge(generators, relators)
    require(len(support) == 22, "wrong reconstructed support size")
    require(stored_support == support, "stored and reconstructed group supports differ")
    columns = tuple(zip(*factor))
    pair_groups = tuple(
        tuple(matmul(inverse(g), h) for h in support) for g in support
    )
    require(len({g for row in pair_groups for g in row}) == 293,
            "wrong support-product class count")
    residual = [[{} for _ in range(6)] for _ in range(6)]
    for i in range(6):
        for j in range(6):
            entry = {g: SCALE * coefficient for g, coefficient in delta[i][j].items()}
            if i == j:
                add_term(entry, IDENTITY, -(SCALE // 250))
            for a in range(22):
                left = columns[22 * i + a]
                for b in range(22):
                    right = columns[22 * j + b]
                    coefficient = sum(x * y for x, y in zip(left, right))
                    add_term(entry, pair_groups[a][b], -coefficient)
            residual[i][j] = entry
    for i in range(6):
        for j in range(6):
            require(residual[i][j] == star(residual[j][i]), "residual is not Hermitian")
    rows = tuple(
        sum(abs(value) for entry in row for value in entry.values())
        for row in residual
    )
    columns_l1 = tuple(
        sum(abs(value) for i in range(6) for value in residual[i][j].values())
        for j in range(6)
    )
    require(rows == EXPECTED_ROWS, "exact residual row sums changed")
    require(columns_l1 == rows, "row and column residual bounds differ")
    gap = SCALE // 250 - max(rows)
    require(gap > SCALE // 500, "certificate does not imply the clean 1/500 gap")
    return {
        "valid": True,
        "arithmetic": "Python arbitrary-precision integers; standard library only",
        "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "generators": 6,
        "relators": 13,
        "fox_chain_zero": True,
        "support": 22,
        "support_product_classes": 293,
        "factor_shape": [102, 132],
        "factor_denominator": 10**8,
        "residual_denominator": SCALE,
        "residual_row_bound_numerators": rows,
        "residual_column_bound_numerators": columns_l1,
        "residual_terms": sum(len(entry) for row in residual for entry in row),
        "residual_hermitian": True,
        "certified_gap_numerator": gap,
        "clean_gap": "1/500",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.certificate), sort_keys=True))


if __name__ == "__main__":
    main()
