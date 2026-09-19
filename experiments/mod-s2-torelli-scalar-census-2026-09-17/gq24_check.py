#!/usr/bin/env python3
"""Identify the level-3 census lattice W with the point-line incidence of GQ(2,4).

Input: census-results-frame-3.json (python3 census.py frame-3), which stores
the 45 class representatives (frame matrices A mod 3) and the HNF basis of
W <= Z^45.

Checks:
 1. The class of a coset depends only on the symplectic splitting of F_3^4
    attached to its frame, and classes <-> the 45 splittings {P, P^perp}.
 2. Call two splittings {P, P'} and {Q, Q'} transverse when all four
    intersections P n Q, P n Q', P' n Q, P' n Q' are zero.  (The other type
    of pair has two of them of dimension one.)  Test: the transversality
    graph has degree 12, and it has exactly 27 cliques of size 5, each
    splitting lying in 3 of them.  That is the incidence pattern of the 45
    lines and 27 points of the generalized quadrangle GQ(2,4).
 3. The 27 point-star vectors (indicator of the 5 splittings through a point)
    lie in W, have rank 21 = rank W, and generate W over Z (index computed).
 4. Each star has augmentation 5, which is the l1 = 5 certificate d >= 1/15.
"""
import itertools
import json
import os
import sys

import numpy as np
from flint import fmpz_mat

P = 3
J = np.array([[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]],
             dtype=np.int64)


def rref(rows):
    A = [[int(t) % P for t in r] for r in rows]
    m, pr = len(A), 0
    for col in range(4):
        piv = next((r for r in range(pr, m) if A[r][col]), None)
        if piv is None:
            continue
        A[pr], A[piv] = A[piv], A[pr]
        inv = pow(A[pr][col], -1, P)
        A[pr] = [(t * inv) % P for t in A[pr]]
        for r in range(m):
            if r != pr and A[r][col]:
                f = A[r][col]
                A[r] = [(a - f * b) % P for a, b in zip(A[r], A[pr])]
        pr += 1
    return tuple(tuple(r) for r in A[:pr])


def perp(rows):
    """Symplectic complement (as a subspace of row vectors, form x J y^T)."""
    M = (np.array(rows, dtype=np.int64) @ J) % P      # constraints on y
    sols = [v for v in itertools.product(range(P), repeat=4)
            if not ((M @ np.array(v)) % P).any()]
    return rref(sols)


def inv_mod(A):
    from sympy import Matrix
    return np.array(Matrix(A.tolist()).inv_mod(P), dtype=np.int64)


def splitting(A, mode):
    if mode == "rows":
        Q = rref(A[0:2])
    elif mode == "cols":
        Q = rref(A[:, 0:2].T)
    elif mode == "inv-rows":
        Q = rref(inv_mod(A)[0:2])
    else:
        Q = rref(inv_mod(A)[:, 0:2].T)
    return frozenset([Q, perp(Q)])


def span(rows):
    """All vectors of the F_3-span of the given rows."""
    return set(tuple(int(x) % P for x in np.array(v) @ np.array(rows))
               for v in itertools.product(range(P), repeat=len(rows)))


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "census-results-frame-3.json")) as f:
        res = json.load(f)[0]
    reps = [np.array(o, dtype=np.int64) for o in res["class_rep_objects"]]
    assert len(reps) == 45
    # 1. find the convention under which the class map factors through
    #    splittings; the coset objects themselves are not stored per coset
    #    except through coset_class, so we re-enumerate them.
    sys.path.insert(0, here)
    import census
    start, step = census.case("frame-3")
    objs, _ = census.enumerate_by_step(start, step)
    cls = res["coset_class"]
    good = None
    for mode in ("rows", "cols", "inv-rows", "inv-cols"):
        seen = {}
        ok = True
        for o, c in zip(objs, cls):
            s = splitting(np.array(o, dtype=np.int64), mode)
            if seen.setdefault(s, c) != c:
                ok = False
                break
        if ok and len(seen) == 45:
            good = mode
            split_of = {c: s for s, c in seen.items()}
            break
    print("convention:", good)
    assert good is not None
    splits = [split_of[c] for c in range(45)]
    # 2. transversality graph: {P, P'} ~ {Q, Q'} iff every one of the four
    #    intersections P n Q, P n Q', P' n Q, P' n Q' is zero.
    spans = [[span(list(Q)) for Q in sorted(s)] for s in splits]
    types = {}
    for i in range(45):
        for j in range(45):
            if i != j:
                types[i, j] = tuple(sorted(len(a & b) for a in spans[i]
                                           for b in spans[j]))
    print("pair types:", sorted(set(types.values())))
    adj = [[i != j and types[i, j] == (1, 1, 1, 1) for j in range(45)]
           for i in range(45)]
    degs = sorted(set(int(sum(r)) for r in adj))
    print("degrees:", degs)
    cliques = set()
    for i in range(45):
        nb = [j for j in range(45) if adj[i][j]]
        for T in itertools.combinations(nb, 4):
            if all(adj[a][b] for a, b in itertools.combinations(T, 2)):
                cliques.add(frozenset((i,) + T))
    cliques = sorted(sorted(c) for c in cliques)
    per_line = [sum(i in c for c in cliques) for i in range(45)]
    print("5-cliques:", len(cliques), "lines per clique-count:",
          sorted(set(per_line)))
    # 3. stars in W, rank, index
    B = res["W_basis"]
    stars = [[1 if i in c else 0 for i in range(45)] for c in cliques]
    HB = fmpz_mat(B).hnf()
    both = fmpz_mat(B + stars).hnf()
    rankW = fmpz_mat(B).rank()
    in_W = both.rank() == rankW and \
        all(both[i, j] == HB[i, j] for i in range(rankW) for j in range(45))
    S = fmpz_mat(stars)
    rank_stars = S.rank()
    HS = S.hnf()
    # index of lattice(stars) in W: ratio of gcd of maximal minors via HNF
    rowsS = [[int(HS[i, j]) for j in range(45)] for i in range(rank_stars)]
    rowsW = [[int(HB[i, j]) for j in range(45)] for i in range(rankW)]
    # express stars lattice in W basis and take |det|
    from sympy import Matrix
    MW = Matrix(rowsW)
    coeffs = Matrix([list(MW.T.solve_least_squares(Matrix(r)))
                     for r in rowsS])
    index = abs(coeffs.det()) if rank_stars == rankW else None
    print("stars in W:", in_W, "rank stars:", rank_stars, "rank W:", rankW,
          "index [W : <stars>]:", index)
    print("star augmentations:", sorted(set(sum(s) for s in stars)))
    out = {"convention": good, "degrees": degs, "n_5_cliques": len(cliques),
           "cliques_per_line": sorted(set(per_line)), "stars_in_W": in_W,
           "rank_stars": rank_stars, "rank_W": rankW,
           "index_W_over_stars": str(index), "cliques": cliques}
    with open(os.path.join(here, "gq24-check-frame-3.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
