#!/usr/bin/env python3
"""Separating-twist relation lattice W(Gamma'') for the index-two subgroups
Gamma'' of Gamma(4) that contain Gamma(8) (first step of the 2-adic tower
beyond Gamma(4)).

Gamma(4)/Gamma(8) = {I + 4Y : Y in sp_4(F_2)}, sp_4(F_2) = {Y : JY symmetric}
(10-dimensional, abelian quotient).  An index-two Gamma'' >= Gamma(8) is
{I + 4Y : f(Y) = 0} . Gamma(8) for a nonzero functional f; Sp_4(Z) acts on the
f by the adjoint action of Sp_4(F_2), and conjugate f give isomorphic data.

Same Birman--Hilden reduction as gamma4.py: M'' = pi^{-1}(Gamma'') is
isomorphic to its image in H = B_5/<<Delta^2>>, and the cosets H/M'' are the
orbit of the class of I in Sp_4(Z/8) / (+-(Gamma''/Gamma(8))), 2 * 61440 of
them.  Canonical form of a class {+-X A}: choose the sign making A mod 4
lexicographically minimal, write A = A0 + 4E (A0 = A mod 4), and reduce
F = E Abar^{-1} in M_4(F_2) modulo ker f (left multiplication by I + 4Y
changes F to F + Y).

Usage: python3 level8_index2.py orbits            (list adjoint orbits of f)
       python3 level8_index2.py run K out.pkl     (reduce for orbit rep K)
"""
import json
import os
import pickle
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-gamma4-torsion-census-2026-09-17"))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
import gamma4 as G4  # noqa: E402

J2 = C.J % 2


def bits(Y):
    return int("".join(str(int(t)) for t in Y.flatten()), 2)


def unbits(x):
    return np.array([(x >> (15 - k)) & 1 for k in range(16)],
                    dtype=np.int64).reshape(4, 4)


def sp_basis():
    out = []
    for i in range(4):
        for j in range(i, 4):
            S = np.zeros((4, 4), dtype=np.int64)
            S[i, j] = S[j, i] = 1
            out.append((J2 @ S) % 2)          # Y = J S, J^{-1} = J mod 2
    return out


def coords(Y, basis):
    """Coordinates of Y in the basis (Y = J S, read off S)."""
    S = (J2 @ Y) % 2
    return [int(S[i, j]) for i in range(4) for j in range(i, 4)]


def sp4_f2():
    mats = [A % 2 for A in C.GENMATS]
    start = tuple(np.eye(4, dtype=np.int64).flatten())
    seen, queue = {start}, [start]
    for o in queue:
        A = np.array(o).reshape(4, 4)
        for B in mats:
            n = tuple(((A @ B) % 2).flatten())
            if n not in seen:
                seen.add(n)
                queue.append(n)
    return [np.array(o).reshape(4, 4) for o in queue]


def inv2(A):
    return (J2 @ A.T @ J2) % 2


def functional_orbits():
    basis = sp_basis()
    group = sp4_f2()
    assert len(group) == 720
    ads = []
    for g in group:
        gi = inv2(g)
        ads.append(np.array([coords((g @ Y @ gi) % 2, basis) for Y in basis],
                            dtype=np.int64))       # row i = Ad(g) Y_i
    todo = set(range(1, 1024))
    orbits = []
    while todo:
        x = min(todo)
        f = np.array([(x >> k) & 1 for k in range(10)], dtype=np.int64)
        orb = set()
        for Ad in ads:
            h = (Ad @ f) % 2          # (f o Ad(g))(Y_i) = f(Ad(g) Y_i)
            orb.add(int(sum(int(h[k]) << k for k in range(10))))
        orbits.append(sorted(orb))
        todo -= orb
    return basis, orbits


def kernel_echelon(fcode, basis):
    f = [(fcode >> k) & 1 for k in range(10)]
    vecs = []
    piv = next(k for k in range(10) if f[k])
    for k in range(10):
        if k == piv:
            continue
        Y = basis[k].copy()
        if f[k]:
            Y = (Y + basis[piv]) % 2
        vecs.append(bits(Y))
    ech = []                                  # (pivot bit, vector)
    for v in vecs:
        for p, w in ech:
            if (v >> p) & 1:
                v ^= w
        if v:
            p = v.bit_length() - 1
            ech = [(q, (w ^ v) if (w >> p) & 1 else w) for q, w in ech]
            ech.append((p, v))
    assert len(ech) == 9
    return ech


def make_canon(ech):
    def reduce(x):
        for p, w in ech:
            if (x >> p) & 1:
                x ^= w
        return x

    def canon(A):
        a = tuple(int(t) % 4 for t in A.flatten())
        b = tuple((-int(t)) % 4 for t in A.flatten())
        s = 1 if a <= b else -1
        As = (s * A) % 8
        A0 = As % 4
        E = (As - A0) // 4
        Ab = A0 % 2
        F = reduce(bits((E @ inv2(Ab)) % 2))
        return (tuple(A0.flatten()), F)

    def rep(key):
        A0 = np.array(key[0], dtype=np.int64).reshape(4, 4)
        return (A0 + 4 * (unbits(key[1]) @ (A0 % 2))) % 8

    return canon, rep


def enumerate_level8(fcode, basis, limit=300000):
    canon, rep = make_canon(kernel_echelon(fcode, basis))
    mats = [A % 8 for A in C.GENMATS[:G4.NG]]
    start = canon(np.eye(4, dtype=np.int64))
    index, objs, act = {start: 0}, [start], []
    q = 0
    while q < len(objs):
        A = rep(objs[q])
        row = []
        for B in mats:
            nb = canon((A @ B) % 8)
            if nb not in index:
                index[nb] = len(objs)
                objs.append(nb)
                if len(objs) > limit:
                    raise RuntimeError("orbit exceeds limit")
            row.append(index[nb])
        act.append(row)
        q += 1
    return objs, act


def reduce_f(fcode, basis):
    t0 = time.time()
    objs, act = enumerate_level8(fcode, basis)
    print(f"f={fcode}: cosets {len(act)} [{time.time()-t0:.1f}s]", flush=True)
    G4.check(act)
    ngen, rels, vs = G4.rs(act)
    print(f"  Schreier gens {ngen}, relators {len(rels)} "
          f"[{time.time()-t0:.1f}s]", flush=True)
    cols, R, V = C.unit_eliminate(ngen, rels, vs)
    del rels
    print(f"  after unit elimination: {len(cols)} gens, {len(R)} relators "
          f"[{time.time()-t0:.1f}s]", flush=True)
    distinct = {}
    for v in V:
        key = tuple(sorted(v.items()))
        distinct[key] = distinct.get(key, 0) + 1
    keys = list(distinct)
    kidx = {k: i for i, k in enumerate(keys)}
    coset_key = [kidx[tuple(sorted(v.items()))] for v in V]
    print(f"  distinct reduced v vectors: {len(keys)}", flush=True)
    return {"f": fcode, "cols": cols, "R": R, "V": [dict(k) for k in keys],
            "mult": [distinct[k] for k in keys], "objs": objs,
            "coset_key": coset_key}


if __name__ == "__main__":
    basis, orbits = functional_orbits()
    if sys.argv[1] == "orbits":
        info = [{"rep": o[0], "size": len(o),
                 "rep_coords_in_JS_basis": [(o[0] >> k) & 1
                                            for k in range(10)]}
                for o in orbits]
        print(json.dumps(info))
    else:
        k = int(sys.argv[2])
        d = reduce_f(orbits[k][0], basis)
        with open(sys.argv[3], "wb") as fh:
            pickle.dump(d, fh)
        print("saved", sys.argv[3])
