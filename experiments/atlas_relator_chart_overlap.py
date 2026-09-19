"""Exact computation of the two-chart overlap in the binary Leavitt atlas.

The canonical regular-A8 criterion uses

    Pbar = K1 * K2 = A8 * A8  --rho-->  Q = L_F2(1,2)^times.

The first natural source of kernel words is the chart overlap: if k lies in
K1 cap K2 (inside Q) and w1, w2 are words expressing it in the two factors,
then w1 w2^{-1} lies in Rbar = ker rho.  Those words normally generate the
kernel of

    K1 * K2  --->>  K1 *_{K1 cap K2} K2,

which is the largest virtually free quotient of Pbar through which rho can
factor chartwise.  This script computes K1 cap K2 exactly.

Method.  K_i is the group of invertible scalar leaf matrices on the four-leaf
prefix code D_i.  Its F2-linear span A_i inside L is 16-dimensional with basis
the monomials delta_u delta_v^*, u,v in D_i.  Two elements of L are compared by
expanding every homogeneous degree to one common right-path depth, which is
exact (it only uses ee^* + ff^* = 1) and injective.  A1 cap A2 is then an
ordinary GF(2) row-space intersection, and

    K1 cap K2 = { g in GL_4(F2) : chart_1(g) in A1 cap A2 }.
"""

import itertools
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_two_chart_search import (  # noqa: E402
    CHART_LEAVES,
    gf2_mul,
    leavitt_chart_element,
    transvection,
)

LEAVES = {factor: [tuple(map(int, leaf)) for leaf in CHART_LEAVES[factor]]
          for factor in (1, 2)}


def basis_monomials(factor):
    leaves = LEAVES[factor]
    return [(u, v) for u in leaves for v in leaves]


def expand(monomial, right_len):
    """Rewrite (a, b) with len(b) = right_len using ee^* + ff^* = 1."""
    a, b = monomial
    extra = right_len - len(b)
    assert extra >= 0
    out = set()
    for suffix in itertools.product((0, 1), repeat=extra):
        term = (a + suffix, b + suffix)
        out ^= {term}
    return out


def canon(element, right_len_by_degree):
    out = set()
    for a, b in element:
        degree = len(a) - len(b)
        out ^= expand((a, b), right_len_by_degree[degree])
    return out


def rref(rows, width):
    """GF(2) row reduction; returns (pivots, reduced rows)."""
    mat = [row.copy() for row in rows]
    pivots = []
    r = 0
    for c in range(width):
        piv = None
        for i in range(r, len(mat)):
            if mat[i][c]:
                piv = i
                break
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        for i in range(len(mat)):
            if i != r and mat[i][c]:
                mat[i] ^= mat[r]
        pivots.append(c)
        r += 1
        if r == len(mat):
            break
    return pivots, mat[:r]


def nullspace(mat, width):
    """Left nullspace basis of a list of GF(2) rows (vectors x with x*M = 0)."""
    height = len(mat)
    augmented = [np.concatenate([mat[i], np.eye(height, dtype=np.uint8)[i]])
                 for i in range(height)]
    _pivots, reduced = rref(augmented, width + height)
    # rows of `reduced` whose first `width` entries vanish record the kernel
    kernel = []
    _p2, full = rref(augmented, width)
    # redo reduction tracking all rows (rref truncates zero rows)
    mat2 = [row.copy() for row in augmented]
    r = 0
    for c in range(width):
        piv = None
        for i in range(r, height):
            if mat2[i][c]:
                piv = i
                break
        if piv is None:
            continue
        mat2[r], mat2[piv] = mat2[piv], mat2[r]
        for i in range(height):
            if i != r and mat2[i][c]:
                mat2[i] ^= mat2[r]
        r += 1
    for i in range(height):
        if not mat2[i][:width].any():
            kernel.append(mat2[i][width:])
    del reduced, full, _pivots, _p2
    return kernel


def main():
    monomials = {factor: basis_monomials(factor) for factor in (1, 2)}

    right_len = {}
    for factor in (1, 2):
        for a, b in monomials[factor]:
            degree = len(a) - len(b)
            right_len[degree] = max(right_len.get(degree, 0), len(b))

    coordinate_index = {}
    vectors = {}
    for factor in (1, 2):
        expanded = [canon({m: 1}, right_len) for m in monomials[factor]]
        vectors[factor] = expanded
        for term_set in expanded:
            for term in term_set:
                coordinate_index.setdefault(term, len(coordinate_index))

    width = len(coordinate_index)
    rows = []
    for factor in (1, 2):
        for term_set in vectors[factor]:
            row = np.zeros(width, dtype=np.uint8)
            for term in term_set:
                row[coordinate_index[term]] = 1
            rows.append(row)

    print("common expansion depth per degree:", dict(sorted(right_len.items())))
    print("ambient monomial coordinates:", width)

    pivots1, _ = rref(rows[:16], width)
    pivots2, _ = rref(rows[16:], width)
    print("dim A1 =", len(pivots1), " dim A2 =", len(pivots2))

    kernel = nullspace(rows, width)
    print("dim of relation space between the two 16-tuples:", len(kernel))

    # Intersection coordinates inside chart 1.
    inter_rows = [vec[:16].copy() for vec in kernel]
    piv, reduced = rref(inter_rows, 16) if inter_rows else ([], [])
    print("dim (A1 cap A2) =", len(piv))
    intersection_basis = [row[:16] for row in reduced]

    # Membership test for chart-1 matrices: the 16 chart-1 coordinates of g are
    # exactly its matrix entries in row-major order.
    if intersection_basis:
        piv_set, red = rref([row.copy() for row in intersection_basis], 16)
    else:
        piv_set, red = [], []

    def in_intersection(matrix):
        vec = matrix.reshape(-1).astype(np.uint8).copy()
        for row, c in zip(red, piv_set):
            if vec[c]:
                vec ^= row
        return not vec.any()

    # Enumerate GL_4(F2).
    gens = [transvection(r, c) for r, c in
            ((0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2))]
    identity = np.eye(4, dtype=np.uint8)
    seen = {identity.tobytes(): identity}
    frontier = [identity]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = gf2_mul(g, s)
                key = h.tobytes()
                if key not in seen:
                    seen[key] = h
                    nxt.append(h)
        frontier = nxt
    print("|GL_4(F2)| =", len(seen))

    overlap = [g for g in seen.values() if in_intersection(g)]
    print("|K1 cap K2| =", len(overlap))

    # Sanity: verify each overlap element really is a chart-2 scalar matrix.
    def chart2_coordinates(g):
        element = leavitt_chart_element(1, g)
        target = canon(element, right_len)
        vec = np.zeros(width, dtype=np.uint8)
        for term in target:
            if term not in coordinate_index:
                return None
            vec[coordinate_index[term]] = 1
        rows2 = [r.copy() for r in rows[16:]]
        rows2.append(vec)
        p_before, _ = rref([r.copy() for r in rows[16:]], width)
        p_after, _ = rref(rows2, width)
        return len(p_after) == len(p_before)

    checked = sum(1 for g in overlap if chart2_coordinates(g))
    print("verified inside span(A2):", checked, "of", len(overlap))

    if 1 < len(overlap) <= 64:
        orders = {}
        for g in overlap:
            p = g.copy()
            k = 1
            while not np.array_equal(p, identity):
                p = gf2_mul(p, g)
                k += 1
            orders[k] = orders.get(k, 0) + 1
        print("element orders in K1 cap K2:", dict(sorted(orders.items())))


if __name__ == "__main__":
    main()
