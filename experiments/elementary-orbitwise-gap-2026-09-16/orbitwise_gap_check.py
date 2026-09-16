#!/usr/bin/env python3
"""Exact check of the orbitwise fixed-point gap for elementary groups over small finite rings.

Theorem G (research/elementary-group-column-actions-have-orbitwise-gap.md): for a unital ring A, a finite
left A-module W and n >= 2, every matrix g in M_n(A) acting on V = W^n, and every EL_n(A)-orbit O,
either g fixes O pointwise or g moves at least |O|/(2n^2) points of O.

For each (ring, module, n) this script
  * builds the ring and module tables and checks the ring and module axioms exhaustively;
  * computes the EL_n(A)-orbits on V from the generators e_ij(a), a in A;
  * runs over matrices g (all of M_n(A) when feasible, otherwise a random sample of matrices together
    with random words in the generators), and for every orbit on which g acts nontrivially records
    the moved fraction;
  * asserts that the minimum moved fraction is >= 1/(2n^2), and prints the observed minimum.

Evidence only for the listed cases; the theorem is proved in the artifact.  Single-threaded, small.
"""
import itertools
import sys

import numpy as np

RNG = np.random.default_rng(20260916)


# ----------------------------------------------------------------------------------------------
# rings and modules as tables
# ----------------------------------------------------------------------------------------------
class Ring:
    def __init__(self, name, size, add, mul, one):
        self.name, self.size, self.add, self.mul, self.one = name, size, add, mul, one
        self.neg = np.array([int(np.where(add[a] == 0)[0][0]) for a in range(size)])
        r = range(size)
        for a in r:
            assert add[a, 0] == a and mul[one, a] == a and mul[a, one] == a
            for b in r:
                assert add[a, b] == add[b, a]
                for c in r:
                    assert add[add[a, b], c] == add[a, add[b, c]]
                    assert mul[mul[a, b], c] == mul[a, mul[b, c]]
                    assert mul[a, add[b, c]] == add[mul[a, b], mul[a, c]]
                    assert mul[add[a, b], c] == add[mul[a, c], mul[b, c]]


class Module:
    def __init__(self, name, ring, size, add, act):
        self.name, self.ring, self.size, self.add, self.act = name, ring, size, add, act
        R = ring
        for w in range(size):
            assert add[w, 0] == w and act[R.one, w] == w
            for v in range(size):
                assert add[w, v] == add[v, w]
                for a in range(R.size):
                    assert act[a, add[w, v]] == add[act[a, w], act[a, v]]
            for a in range(R.size):
                for b in range(R.size):
                    assert act[R.mul[a, b], w] == act[a, act[b, w]]
                    assert act[R.add[a, b], w] == add[act[a, w], act[b, w]]


def f2_algebra(name, dim, prod, one_mask):
    """prod[i][j] = bitmask of basis_i * basis_j."""
    size = 1 << dim
    add = np.array([[a ^ b for b in range(size)] for a in range(size)], dtype=np.int64)
    mul = np.zeros((size, size), dtype=np.int64)
    for a in range(size):
        for b in range(size):
            m = 0
            for i in range(dim):
                if a >> i & 1:
                    for j in range(dim):
                        if b >> j & 1:
                            m ^= prod[i][j]
            mul[a, b] = m
    return Ring(name, size, add, mul, one_mask)


def f2_module(name, ring, dim, basis_act):
    """basis_act[i] = function on bitmasks, the action of the i-th basis element of the ring."""
    size = 1 << dim
    add = np.array([[a ^ b for b in range(size)] for a in range(size)], dtype=np.int64)
    rdim = ring.size.bit_length() - 1
    act = np.zeros((ring.size, size), dtype=np.int64)
    for a in range(ring.size):
        for w in range(size):
            m = 0
            for i in range(rdim):
                if a >> i & 1:
                    m ^= basis_act[i](w)
            act[a, w] = m
    return Module(name, ring, size, add, act)


def regular_module(ring):
    return Module("A (left regular)", ring, ring.size, ring.add.copy(), ring.mul.copy())


def truncated_poly(k):
    prod = [[(1 << (i + j)) if i + j < k else 0 for j in range(k)] for i in range(k)]
    return f2_algebra(f"F_2[t]/(t^{k})", k, prod, 1)


def square_zero_xy():
    # basis 1, x, y with all products of x, y zero
    prod = [[1, 2, 4], [2, 0, 0], [4, 0, 0]]
    return f2_algebra("F_2[x,y]/(x,y)^2", 3, prod, 1)


def upper_triangular_2():
    # basis E11 (bit0), E12 (bit1), E22 (bit2)
    E11, E12, E22 = 1, 2, 4
    prod = [[E11, E12, 0], [0, 0, E12], [0, 0, E22]]
    return f2_algebra("T_2(F_2)", 3, prod, E11 | E22)


def noncomm_16():
    # F_2<x,y>/(x^2, y^2, yx, all words of length 3): basis 1, x, y, xy
    one, x, y, xy = 1, 2, 4, 8
    prod = [[one, x, y, xy], [x, 0, xy, 0], [y, 0, 0, 0], [xy, 0, 0, 0]]
    return f2_algebra("F_2<x,y>/(x^2,y^2,yx,deg 3)", 4, prod, one)


def z4():
    size = 4
    add = np.array([[(a + b) % 4 for b in range(4)] for a in range(4)], dtype=np.int64)
    mul = np.array([[(a * b) % 4 for b in range(4)] for a in range(4)], dtype=np.int64)
    return Ring("Z/4", size, add, mul, 1)


def f2():
    return f2_algebra("F_2", 1, [[1]], 1)


def t2_natural(ring):
    # columns (e1 = bit0, e2 = bit1); E11 e1 = e1, E12 e2 = e1, E22 e2 = e2
    acts = [lambda w: w & 1, lambda w: (w >> 1) & 1, lambda w: w & 2]
    return f2_module("F_2^2 (natural)", ring, 2, acts)


def a_plus_a_mod_t(ring):
    # over F_2[t]/(t^2): W = A (bits 0,1) + A/(t) (bit 2); t kills the second summand
    acts = [lambda w: w, lambda w: ((w & 1) << 1)]
    return f2_module("A + A/(t)", ring, 3, acts)


# ----------------------------------------------------------------------------------------------
# the check
# ----------------------------------------------------------------------------------------------
def run_case(ring, mod, n, sample_pairs=1500, words=1500):
    A, W = ring, mod
    q, w = A.size, W.size
    nV = w ** n
    X = np.array([[(v // w ** k) % w for k in range(n)] for v in range(nV)], dtype=np.int64)
    nrows = q ** n
    rows = np.array([[(r // q ** j) % q for j in range(n)] for r in range(nrows)], dtype=np.int64)
    # R[r, x] = sum_j act(r_j, x_j) in W
    R = np.zeros((nrows, nV), dtype=np.int64)
    for j in range(n):
        term = W.act[rows[:, j][:, None], X[None, :, j]]
        R = W.add[R, term]
    F = [(R == X[None, :, k]) for k in range(n)]  # F[k][r, x]: row r reproduces coordinate k of x

    def row_index(entries):
        return int(sum(int(entries[j]) * q ** j for j in range(n)))

    ident_rows = [row_index([A.one if j == k else 0 for j in range(n)]) for k in range(n)]
    gens = []
    gen_mats = []
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            for a in range(1, q):
                rr = list(ident_rows)
                ent = [A.one if jj == i else 0 for jj in range(n)]
                ent[j] = a
                rr[i] = row_index(ent)
                y = sum(R[rr[k]] * w ** k for k in range(n))
                gens.append(y)
                M = np.zeros((n, n), dtype=np.int64)
                for k in range(n):
                    M[k, k] = A.one
                M[i, j] = a
                gen_mats.append(M)
    # orbits by label propagation
    lab = np.arange(nV)
    while True:
        old = lab.copy()
        for p in gens:
            lab = np.minimum(lab, lab[p])
            np.minimum.at(lab, p, lab.copy())
        lab = lab[lab]
        if np.array_equal(lab, old):
            break
    reps, comp = np.unique(lab, return_inverse=True)
    norb = len(reps)
    sizes = np.bincount(comp, minlength=norb)
    Ind = np.zeros((norb, nV), dtype=np.float32)
    Ind[comp, np.arange(nV)] = 1.0
    # sanity: orbits are invariant under generators
    for p in gens:
        assert np.array_equal(comp[p], comp)

    best = [2.0, None]

    def consume(fixed_block, first_rows):
        # fixed_block: (m, nV) booleans for matrices whose first n-1 rows are first_rows and last row index m
        moved = (~fixed_block).astype(np.float32)
        counts = moved @ Ind.T  # (m, norb)
        frac = counts / sizes[None, :]
        frac[counts == 0] = 2.0
        idx = np.unravel_index(np.argmin(frac), frac.shape)
        if frac[idx] < best[0]:
            best[0] = float(frac[idx])
            best[1] = (tuple(first_rows) + (int(idx[0]),), int(reps[idx[1]]), int(sizes[idx[1]]),
                       int(round(counts[idx])))

    mode = "exhaustive" if q ** (n * n) * nV <= 2 * 10 ** 8 else "sampled"
    nmat = 0
    if mode == "exhaustive":
        for first in itertools.product(range(nrows), repeat=n - 1):
            base = np.ones(nV, dtype=bool)
            for k, r in enumerate(first):
                base &= F[k][r]
            consume(base[None, :] & F[n - 1], first)
            nmat += nrows
    else:
        for _ in range(sample_pairs):
            first = tuple(int(v) for v in RNG.integers(0, nrows, size=n - 1))
            base = np.ones(nV, dtype=bool)
            for k, r in enumerate(first):
                base &= F[k][r]
            consume(base[None, :] & F[n - 1], first)
            nmat += nrows
    # random words in the generators (group elements), always
    def matmul(M1, M2):
        P = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            for j in range(n):
                s = 0
                for k in range(n):
                    s = A.add[s, A.mul[M1[i, k], M2[k, j]]]
                P[i, j] = s
        return P
    for _ in range(words):
        M = np.eye(n, dtype=np.int64) * A.one
        for _ in range(int(RNG.integers(1, 25))):
            M = matmul(M, gen_mats[int(RNG.integers(0, len(gen_mats)))])
        rr = [row_index(M[k]) for k in range(n)]
        fixed = np.ones(nV, dtype=bool)
        for k in range(n):
            fixed &= F[k][rr[k]]
        consume(fixed[None, :], tuple(rr[:-1]))
        nmat += 1
    bound = 1.0 / (2 * n * n)
    ok = best[0] >= bound - 1e-12
    print(f"{A.name:32s} W={W.name:18s} n={n}  |V|={nV:5d}  orbits={norb:3d}  mode={mode:10s} "
          f"matrices={nmat:8d}  min moved fraction={best[0]:.4f}  bound 1/(2n^2)={bound:.4f}  "
          f"{'OK' if ok else 'VIOLATION'}  witness(rows, orbit rep, |O|, moved)={best[1]}")
    sys.stdout.flush()
    assert ok, "orbitwise gap bound violated"
    return best[0]


def main():
    F2 = f2()
    T2 = truncated_poly(2)
    T3 = truncated_poly(3)
    SZ = square_zero_xy()
    UT = upper_triangular_2()
    NC = noncomm_16()
    Z4 = z4()
    cases = [
        (F2, regular_module(F2), 2), (F2, regular_module(F2), 3),
        (T2, regular_module(T2), 2), (T2, regular_module(T2), 3),
        (Z4, regular_module(Z4), 2), (Z4, regular_module(Z4), 3),
        (T2, a_plus_a_mod_t(T2), 2), (T2, a_plus_a_mod_t(T2), 3),
        (T3, regular_module(T3), 2), (T3, regular_module(T3), 3),
        (SZ, regular_module(SZ), 2), (SZ, regular_module(SZ), 3),
        (UT, t2_natural(UT), 2), (UT, t2_natural(UT), 3),
        (UT, regular_module(UT), 2), (UT, regular_module(UT), 3),
        (NC, regular_module(NC), 2),
    ]
    mins = []
    for ring, mod, n in cases:
        mins.append(run_case(ring, mod, n))
    print(f"all {len(cases)} cases satisfy the bound; overall minimum moved fraction {min(mins):.4f}")


if __name__ == "__main__":
    main()
