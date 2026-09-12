#!/usr/bin/env python3
"""Exact finite-field audit of the binary Schur--Toeplitz embedding.

The smallest forbidden Schur block is ``I=M_2(F_p)`` and its corrected child
is the diagonal algebra ``C=F_p direct_sum F_p``.  The Morita embedding

    I -> M_2(C),       a -> a tensor I_2

uses the Toeplitz head coordinate for the old full-block coordinate and keeps
the child sign as a duplicated branch.  This script exhausts the multiplication
table over F_5 and checks the induced substitution on finite matrix heads.

It deliberately uses only the Python standard library.  The output is a small
JSON certificate consumed by the corresponding Cairn claim.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


P = 5


def matmul(a, b):
    n = len(a)
    m = len(b)
    k = len(b[0])
    return [
        [sum(a[i][t] * b[t][j] for t in range(m)) % P for j in range(k)]
        for i in range(n)
    ]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def matrices_2():
    for entries in itertools.product(range(P), repeat=4):
        yield [list(entries[:2]), list(entries[2:])]


def phi(a):
    """Return a tensor I_2 in the (head, child-sign) basis."""
    out = [[0] * 4 for _ in range(4)]
    for r in range(2):
        for beta in range(2):
            for s in range(2):
                out[2 * r + beta][2 * s + beta] = a[r][s] % P
    return out


def basis_matrix(n, i, j):
    out = [[0] * n for _ in range(n)]
    out[i][j] = 1
    return out


def head_substitution(a):
    """Duplicate M_(2N) along the retained child-sign coordinate."""
    size = len(a)
    if size % 2:
        raise ValueError("input head must have size 2N")
    n = size // 2
    out = [[0] * (4 * n) for _ in range(4 * n)]
    for i in range(n):
        for alpha in range(2):
            for j in range(n):
                for gamma in range(2):
                    value = a[2 * i + alpha][2 * j + gamma] % P
                    for beta in range(2):
                        row = 2 * (2 * i + alpha) + beta
                        col = 2 * (2 * j + gamma) + beta
                        out[row][col] = value
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    all_matrices = list(matrices_2())
    images = {tuple(sum(phi(a), [])) for a in all_matrices}
    multiplicative_pairs = 0
    for a in all_matrices:
        for b in all_matrices:
            assert phi(matmul(a, b)) == matmul(phi(a), phi(b))
            multiplicative_pairs += 1

    assert len(images) == P ** 4
    assert phi(eye(2)) == eye(4)

    # Exhaust matrix-unit multiplication for two input Toeplitz sites.  The
    # substitution is the blockwise amplification A -> A tensor I_2, up to
    # the explicit binary-site permutation encoded above.
    input_size = 4
    units = [
        (i, j, basis_matrix(input_size, i, j))
        for i in range(input_size)
        for j in range(input_size)
    ]
    matrix_unit_products = 0
    for i, j, eij in units:
        for k, ell, ekl in units:
            lhs = matmul(head_substitution(eij), head_substitution(ekl))
            expected = (
                head_substitution(basis_matrix(input_size, i, ell))
                if j == k
                else [[0] * 8 for _ in range(8)]
            )
            assert lhs == expected
            matrix_unit_products += 1

    assert head_substitution(eye(input_size)) == eye(8)

    carrier_sites = {}
    sites = {0}
    for depth in range(8):
        carrier_sites[str(depth)] = sorted(sites)
        assert sites == set(range(2 ** depth))
        sites = {2 * i + bit for i in sites for bit in (0, 1)}

    result = {
        "field": "F_5",
        "forbidden_block": "M_2(F_5)",
        "child_block": "F_5 direct_sum F_5",
        "phi_formula": "a -> a tensor I_2 (head coordinate first)",
        "phi_domain_size": len(all_matrices),
        "phi_image_size": len(images),
        "multiplicative_pairs_checked": multiplicative_pairs,
        "matrix_unit_products_checked": matrix_unit_products,
        "head_substitution": "M_4(F_5) -> M_8(F_5)",
        "carrier_sites_by_depth": carrier_sites,
        "all_checks_passed": True,
    }
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
