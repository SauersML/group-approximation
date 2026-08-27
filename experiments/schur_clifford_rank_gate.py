#!/usr/bin/env python3
"""Construct and verify the Schur--Clifford rank compiler over F_2.

For a Boolean predicate f:{0,1}^k->{0,1}, construct an affine-linear
square matrix M_f(x) such that rank_F2 M_f(x)=N+f(x) on the Boolean cube.

The construction uses a disjoint-path algebraic branching program computing
f as the sum of assignment indicators, followed by a Schur-complement rank
linearization.
"""
from __future__ import annotations

from itertools import product
from typing import Dict, Iterable, List, Sequence, Tuple

BitTuple = Tuple[int, ...]
# An affine form c + sum_i a_i x_i over F_2, represented by (c, coeffs).
Affine = Tuple[int, BitTuple]


def affine_zero(k: int) -> Affine:
    return (0, (0,) * k)


def affine_one(k: int) -> Affine:
    return (1, (0,) * k)


def affine_add(a: Affine, b: Affine) -> Affine:
    return (a[0] ^ b[0], tuple(x ^ y for x, y in zip(a[1], b[1])))


def literal(k: int, i: int, bit: int) -> Affine:
    """Indicator literal [x_i=bit]: x_i if bit=1, 1+x_i if bit=0."""
    coeff = [0] * k
    coeff[i] = 1
    return (0 if bit else 1, tuple(coeff))


def eval_affine(a: Affine, x: BitTuple) -> int:
    out = a[0]
    for c, xi in zip(a[1], x):
        out ^= c & xi
    return out


def rank_f2(A: List[List[int]]) -> int:
    A = [row[:] for row in A]
    if not A:
        return 0
    m, n = len(A), len(A[0])
    r = 0
    for c in range(n):
        pivot = next((i for i in range(r, m) if A[i][c] & 1), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        for i in range(m):
            if i != r and A[i][c]:
                A[i] = [u ^ v for u, v in zip(A[i], A[r])]
        r += 1
        if r == m:
            break
    return r


def build_rank_compiler(k: int, satisfying: Iterable[BitTuple]) -> Tuple[List[List[Affine]], int, int, int]:
    """Return (M, baseline_rank, source, sink).

    Build a DAG with one source and one sink and a vertex-disjoint internal
    path for every satisfying assignment. The path product is the assignment
    indicator. If N is its affine weighted adjacency matrix, U=I+N is
    unitriangular and (U^{-1})[s,t]=f(x) on {0,1}^k.

    Then M = [[U, e_t], [e_s^T, 0]]. Since U is invertible,
    rank M = |V| + f(x).
    """
    sats = list(satisfying)
    s = 0
    t = 1
    next_v = 2
    edges: List[Tuple[int, int, Affine]] = []

    if k == 0:
        # Constant predicate. A direct edge has label 1 for true.
        if sats:
            edges.append((s, t, affine_one(0)))
    else:
        for a in sats:
            if len(a) != k:
                raise ValueError("assignment has wrong arity")
            internal = list(range(next_v, next_v + max(0, k - 1)))
            next_v += len(internal)
            path = [s] + internal + [t]
            for i in range(k):
                edges.append((path[i], path[i + 1], literal(k, i, a[i])))

    # Topological order must put s first and t last. Internal path vertices
    # were allocated after t, so reorder as s, all internal vertices, t.
    old_vertices = [s] + list(range(2, next_v)) + [t]
    relabel = {old: new for new, old in enumerate(old_vertices)}
    n = len(old_vertices)

    N = [[affine_zero(k) for _ in range(n)] for _ in range(n)]
    for u_old, v_old, lab in edges:
        u, v = relabel[u_old], relabel[v_old]
        N[u][v] = affine_add(N[u][v], lab)

    U = [[N[i][j] for j in range(n)] for i in range(n)]
    for i in range(n):
        U[i][i] = affine_add(U[i][i], affine_one(k))  # I+N = I-N in F2

    m = n + 1
    M = [[affine_zero(k) for _ in range(m)] for _ in range(m)]
    for i in range(n):
        for j in range(n):
            M[i][j] = U[i][j]

    s_new, t_new = relabel[s], relabel[t]
    M[t_new][n] = affine_one(k)   # top-right e_t
    M[n][s_new] = affine_one(k)   # bottom-left e_s^T
    # bottom-right is 0
    return M, n, s_new, t_new


def eval_matrix(M: List[List[Affine]], x: BitTuple) -> List[List[int]]:
    return [[eval_affine(a, x) for a in row] for row in M]


def truth_table_from_callable(k: int, f) -> Dict[BitTuple, int]:
    return {x: int(bool(f(*x))) for x in product((0, 1), repeat=k)}


def verify_truth_table(table: Dict[BitTuple, int]) -> Tuple[int, int]:
    if not table:
        raise ValueError("truth table must be nonempty")
    k = len(next(iter(table)))
    sats = [x for x, v in table.items() if v]
    M, baseline, _, _ = build_rank_compiler(k, sats)
    for x in product((0, 1), repeat=k):
        got = rank_f2(eval_matrix(M, x))
        want = baseline + table[x]
        if got != want:
            raise AssertionError((x, got, want))
    return len(M), baseline


def verify_small_exhaustive(max_k: int = 3) -> None:
    for k in range(1, max_k + 1):
        cube = list(product((0, 1), repeat=k))
        for mask in range(1 << len(cube)):
            table = {x: (mask >> i) & 1 for i, x in enumerate(cube)}
            verify_truth_table(table)
        print(f"exhaustive k={k}: verified all {1 << len(cube)} predicates")


def and_gate_demo() -> None:
    # Minimal special-purpose AND gate: [[1,x],[y,0]], determinant=xy and
    # the fixed 1-pivot makes rank exactly 1+xy.
    print("AND gate M(x,y)=[[1,x],[y,0]]")
    for x, y in product((0, 1), repeat=2):
        A = [[1, x], [y, 0]]
        print((x, y), "rank=", rank_f2(A), "target=", 1 + x * y)


if __name__ == "__main__":
    and_gate_demo()
    verify_small_exhaustive(3)

    # A non-affine sample: exactly-one-of-three.
    t = truth_table_from_callable(3, lambda x, y, z: x + y + z == 1)
    size, baseline = verify_truth_table(t)
    print(f"one-hot-3: compiler matrix size {size}, baseline rank {baseline}; verified")
