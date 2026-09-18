#!/usr/bin/env python3
"""Integral separating-twist relation lattice W(Gamma(4)) for Mod(S_2).

Reduction (Birman--Hilden).  M/<iota> = Mod(S_{0,6}); iota maps to -I.
M_4 = pi^{-1}Gamma(4) meets <iota> trivially, so M_4 is isomorphic to its image
K4 = ker(Mod(S_{0,6}) -> Sp_4(Z/4)/{+-I}).  K4 lies in the pure group, hence in
H = Stab(puncture 6) = B_5/<<Delta^2>>, Delta^2 = (s1 s2 s3 s4)^5 (capping).
Every separating curve of S_2 covers a 3|3 curve of S_{0,6}, and every 3|3
curve has one side avoiding puncture 6, so all separating twists are
H-conjugates of t_s = (s1 s2)^6.  Hence

    classes v_c = [g t_s g^{-1}] in H_1(K4) = H_1(M_4),  g over H/K4,

and W(Gamma(4)) is their relation lattice, computed by abelianised
Reidemeister--Schreier on the |H/K4| cosets (expected 120 * 512 = 61440).
Uses unit_eliminate / w_lattice / distance_milp / best_certificate from the
level census script (same conventions).
"""
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402

NG = 4                                   # s1..s4 = letters 0..3
T_S = [0, 1] * 6


def relators_H():
    rels = []
    for i in range(NG - 1):
        rels.append(([i, i + 1, i], [i + 1, i, i + 1]))
    for i in range(NG):
        for j in range(i + 2, NG):
            rels.append(([i, j], [j, i]))
    rels.append(([0, 1, 2, 3] * 5, []))  # Delta^2 = 1 (boundary capped)
    return rels


def canon_pm(A, N):
    a = tuple(int(t) % N for t in A.flatten())
    b = tuple((-int(t)) % N for t in A.flatten())
    return min(a, b)


def enumerate_Q(N=4, limit=200000):
    """Right regular action of the image of H in Sp_4(Z/N)/{+-I}."""
    mats = [C.GENMATS[i] % N for i in range(NG)]
    start = canon_pm(np.eye(4, dtype=np.int64), N)
    index, objs, act = {start: 0}, [start], []
    q = 0
    while q < len(objs):
        A = np.array(objs[q], dtype=np.int64).reshape(4, 4)
        row = []
        for B in mats:
            nb = canon_pm((A @ B) % N, N)
            if nb not in index:
                index[nb] = len(objs)
                objs.append(nb)
                if len(objs) > limit:
                    raise RuntimeError("orbit exceeds limit")
            row.append(index[nb])
        act.append(row)
        q += 1
    return objs, act


def check(act):
    for u, v in relators_H():
        for c in range(len(act)):
            assert C.trace_perm(act, c, u) == C.trace_perm(act, c, v)
    for c in range(len(act)):
        assert C.trace_perm(act, c, T_S) == c


def schreier(act):
    k = len(act)
    seen = [False] * k
    seen[0] = True
    tree = set()
    queue = [0]
    for c in queue:
        for i in range(NG):
            d = act[c][i]
            if not seen[d]:
                seen[d] = True
                tree.add((c, i))
                queue.append(d)
    assert all(seen)
    gen = {}
    for c in range(k):
        for i in range(NG):
            if (c, i) not in tree:
                gen[(c, i)] = len(gen)
    return gen


def rs(act):
    gen = schreier(act)
    rels = []
    for u, v in relators_H():
        for c in range(len(act)):
            vec, neg = {}, {}
            e1 = C.trace_word(act, gen, c, u, vec)
            e2 = C.trace_word(act, gen, c, v, neg)
            assert e1 == e2
            for g, a in neg.items():
                vec[g] = vec.get(g, 0) - a
            vec = {g: a for g, a in vec.items() if a}
            if vec:
                rels.append(vec)
    vs = []
    for c in range(len(act)):
        vec = {}
        assert C.trace_word(act, gen, c, T_S, vec) == c
        vs.append({g: a for g, a in vec.items() if a})
    return len(gen), rels, vs


def reduce_level(N):
    t0 = time.time()
    objs, act = enumerate_Q(N)
    check(act)
    ngen, rels, vs = rs(act)
    print(f"N={N}: cosets {len(act)}, Schreier gens {ngen}, relators "
          f"{len(rels)}  [{time.time() - t0:.1f}s]", flush=True)
    cols, R, V = C.unit_eliminate(ngen, rels, vs)
    print(f"  after unit elimination: {len(cols)} gens, {len(R)} relators "
          f"[{time.time() - t0:.1f}s]", flush=True)
    distinct = {}
    for v in V:
        key = tuple(sorted(v.items()))
        distinct[key] = distinct.get(key, 0) + 1
    keys = list(distinct)
    kidx = {k: i for i, k in enumerate(keys)}
    coset_key = [kidx[tuple(sorted(v.items()))] for v in V]
    print(f"  distinct reduced v vectors: {len(keys)}", flush=True)
    return (act, cols, R, [dict(k) for k in keys], [distinct[k] for k in keys],
            objs, coset_key)


if __name__ == "__main__":
    import pickle
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    out = sys.argv[2] if len(sys.argv) > 2 else f"reduced-N{N}.pkl"
    act, cols, R, V, mult, objs, coset_key = reduce_level(N)
    with open(out, "wb") as f:
        pickle.dump({"cols": cols, "R": R, "V": V, "mult": mult,
                     "objs": objs, "coset_key": coset_key}, f)
    print("saved", out)
