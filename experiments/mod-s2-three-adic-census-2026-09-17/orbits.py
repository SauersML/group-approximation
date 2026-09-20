#!/usr/bin/env python3
"""Index-3 subgroups Gamma(9) < G_Y < Gamma(3) of Sp_4(Z), up to conjugacy.

Gamma(3)/Gamma(9) = sp_4(F_3) via I + 3X -> X mod 3 (an Sp_4-equivariant
isomorphism).  Characters are chi_Y(X) = tr(Y X), Y in sp_4(F_3) (the trace
form is nondegenerate on sp_4(F_3)); G_Y = ker chi_Y, and G_Y = G_{-Y}.
Conjugacy classes of the G_Y are adjoint orbits of Y != 0 up to sign.

For a level-3 splitting s = P + P^perp, Stab_{Gamma(3)}(s) maps onto the
block-diagonal subalgebra d(s) = sp(P) + sp(P^perp).  chi_Y is trivial on it
iff Y is in d(s)^perp = off(s) = {Y : Y P <= P^perp, Y P^perp <= P}.  The
number n_Y of such s is the number of level-3 twist classes that split into
three G_Y-classes, and dim H_1(M_3; C_chi) <= n_Y (see the node).
"""
import itertools
import json
import os

import numpy as np

P = 3
J = np.array([[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]])
CHAIN = [np.array(v) for v in
         ([0, 1, 0, 0], [1, 0, 0, 0], [0, 1, 0, 1], [0, 0, 1, 0], [0, 0, 0, 1])]
GENS = [(np.eye(4, dtype=int) + np.outer(x, x @ J)) % P for x in CHAIN]


def inv_mod(A):
    # symplectic: A^{-1} = -J A^T J
    return (-J @ A.T @ J) % P


SYM_IDX = [(i, j) for i in range(4) for j in range(i, 4)]


def from_code(code):
    S = np.zeros((4, 4), dtype=int)
    for k, (i, j) in enumerate(SYM_IDX):
        a = (code // P ** k) % P
        S[i, j] = S[j, i] = a
    return (-J @ S) % P


def to_code(X):
    S = (J @ X) % P                      # J X = J(-J S) = S
    assert (S == S.T).all()
    return sum(int(S[i, j]) * P ** k for k, (i, j) in enumerate(SYM_IDX))


def planes():
    vecs = [np.array(v) for v in itertools.product(range(P), repeat=4) if any(v)]
    seen = set()
    out = []
    for u, v in itertools.combinations(vecs, 2):
        if int(u @ J @ v) % P == 0:
            continue
        # canonical: set of nonzero vectors of span
        span = frozenset(tuple((a * u + b * v) % P) for a in range(P)
                         for b in range(P) if a or b)
        if span in seen:
            continue
        seen.add(span)
        out.append((u, v))
    return out


def perp_basis(u, v):
    sols = [np.array(w) for w in itertools.product(range(P), repeat=4)
            if any(w) and int(u @ J @ np.array(w)) % P == 0
            and int(v @ J @ np.array(w)) % P == 0]
    a = sols[0]
    b = next(w for w in sols if int(a @ J @ w) % P)
    return a, b


def in_span(w, basis):
    return any(((x * basis[0] + y * basis[1] - w) % P == 0).all()
               for x in range(P) for y in range(P))


def main():
    NC = P ** 10
    X = [from_code(c) for c in range(NC)]
    assert all(to_code(X[c]) == c for c in range(0, NC, 97))
    # orbits of Y under conjugation, up to sign
    parent = list(range(NC))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    ginv = [inv_mod(A) for A in GENS]
    for c in range(1, NC):
        Y = X[c]
        for A, Ai in zip(GENS, ginv):
            d = to_code((A @ Y @ Ai) % P)
            ra, rb = find(c), find(d)
            if ra != rb:
                parent[ra] = rb
        d = to_code((-Y) % P)
        ra, rb = find(c), find(d)
        if ra != rb:
            parent[ra] = rb
    orbits = {}
    for c in range(1, NC):
        orbits.setdefault(find(c), []).append(c)
    spl = []
    seen = set()
    for u, v in planes():
        a, b = perp_basis(u, v)
        key = frozenset([
            frozenset(tuple((x * u + y * v) % P) for x in range(P) for y in range(P)),
            frozenset(tuple((x * a + y * b) % P) for x in range(P) for y in range(P))])
        if key in seen:
            continue
        seen.add(key)
        spl.append(((u, v), (a, b)))
    assert len(spl) == 45
    res = []
    for rep, members in sorted(orbits.items(), key=lambda t: len(t[1])):
        Y = X[members[0]]
        n = 0
        for (Pb, Qb) in spl:
            ok = all(in_span((Y @ w) % P, Qb) for w in Pb) and \
                 all(in_span((Y @ w) % P, Pb) for w in Qb)
            n += ok
        Yz = Y.copy()
        rk = int(np.linalg.matrix_rank(Yz))  # rational rank, informative only
        Y2 = (Y @ Y) % P
        res.append({"rep_code": members[0], "size_with_sign": len(members),
                    "n_Y": n, "Y": Y.tolist(),
                    "Y2_zero": bool((Y2 == 0).all()),
                    "charpoly_mod3": [int(round(t)) % P for t in np.poly(Y)]})
    print(len(res), "orbits of nonzero Y up to sign")
    tot = 0
    for r in res:
        print(r["size_with_sign"], "n_Y =", r["n_Y"], "Y^2=0:", r["Y2_zero"],
              "charpoly", r["charpoly_mod3"])
        tot += r["size_with_sign"] * r["n_Y"]
    print("sum over nonzero Y of n_Y =", tot, "(expect 45*80 = 3600)")
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "orbits.json"), "w") as f:
        json.dump(res, f, indent=1)


if __name__ == "__main__":
    main()
