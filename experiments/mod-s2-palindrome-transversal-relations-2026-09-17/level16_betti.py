#!/usr/bin/env python3
"""b_1 of M_16 = pi^-1(Gamma(16)) through Shapiro over A = Gamma(4)/Gamma(16).

(I + 4X)(I + 4X') = I + 4(X + X') mod 16, so A = Gamma(4)/Gamma(16) is
abelian, A = sp4(Z/4) = Sym_4(Z/4) (Y = JX), of order 4^10.  Torelli lies in
M_16, so M_4/M_16 = A and by Shapiro

    b_1(M_16) = sum_{f in A^}  dim_C H_1(M_4; C_f),   C_f(I+4X) = i^(f . Y).

Conjugation by Mod(S_2) acts on A by Y -> g^-T Y g^-1 (g in Sp_4(Z/4)) and
permutes the characters; the twisted Betti number is constant on orbits.
M_4 = K4 in Pbar (Birman-Hilden; -I not in Gamma(4)).

For each orbit representative f we build the twisted Fox matrix of the
512-coset presentation of K4 over F_p (p = 998244353, i -> sqrt(-1) mod p)
and compute its rank by sparse elimination (every nonzero entry is a unit).
Since the entries lie in Z[i], rank mod p <= rank over Q(i), so
dim_Fp coker >= dim_C H_1(K4, *; C_f) = b_1^f + 1 (f != 0).  Hence
dim_Fp coker = 1 certifies b_1^f = 0 exactly.  (Upper bounds only; a larger
cokernel would need a second prime or an exact Z[i] computation.)

    python3 level16_betti.py out.json [orbits]
"""
import itertools
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
import pure as P  # noqa: E402
import palindrome as L  # noqa: E402
import between48 as B48  # noqa: E402

J = C.J
PR = 998244353
IOTA = pow(3, (PR - 1) // 4, PR)          # 3 is a primitive root mod PR
assert IOTA * IOTA % PR == PR - 1
IPOW = np.array([pow(IOTA, k, PR) for k in range(4)], dtype=np.int64)
UT = [(a, b) for a in range(4) for b in range(a, 4)]      # 10 coordinates


def ycoord(X):
    Y = (J @ X) % 4
    assert ((Y - Y.T) % 4 == 0).all(), "not in sp4(Z/4)"
    return np.array([Y[a, b] for a, b in UT], dtype=np.int64)


def schreier_images16():
    mats = B48.pure_mats()
    I = np.eye(4, dtype=np.int64)
    R = {}
    for c in range(len(L.ACT)):
        M = I.copy()
        for a in L.REP[c]:
            M = (M @ mats[a - 1]) % 16
        R[c] = M
    Rinv = {c: (-J @ M.T @ J) % 16 for c, M in R.items()}
    phi = {}
    for c in range(len(L.ACT)):
        for p in range(len(mats)):
            d = L.ACT[c][p]
            M = (R[c] @ mats[p] @ Rinv[d]) % 16
            if ((M - I) % 4).any():
                M = (-M) % 16
                assert not ((M - I) % 4).any(), "Schreier element not in K4"
            y = ycoord(((M - I) // 4) % 4)
            if (c, p) not in L.GEN:
                assert not y.any(), "tree edge with nontrivial image"
            phi[(c, p)] = y
    return phi


def relator_terms(phi):
    """For every (relator, coset): list of (gen, sign, position in A)."""
    rels = [(u, v) for u, v in P.check_presentation()]
    rels.append((P.delta2_pure(), ()))
    out = []
    for u, v in rels:
        w = tuple(u) + P.finv(v)
        for c0 in range(len(L.ACT)):
            c = c0
            pos = np.zeros(10, dtype=np.int64)
            terms = []
            for a in w:
                p = abs(a) - 1
                if a > 0:
                    g = L.GEN.get((c, p))
                    if g is not None:
                        terms.append((g, 1, pos.copy()))
                    pos = (pos + phi[(c, p)]) % 4
                    c = L.ACT[c][p]
                else:
                    d = L.ACT[c][p]
                    pos = (pos - phi[(d, p)]) % 4
                    g = L.GEN.get((d, p))
                    if g is not None:
                        terms.append((g, -1, pos.copy()))
                    c = d
            assert c == c0 and not pos.any(), "relator not closed in A-cover"
            if terms:
                out.append(terms)
    # flatten
    row_id, gen, sgn, P4 = [], [], [], []
    for r, terms in enumerate(out):
        for g, s, pp in terms:
            row_id.append(r)
            gen.append(g)
            sgn.append(s)
            P4.append(pp)
    return (len(out), np.array(row_id), np.array(gen), np.array(sgn),
            np.array(P4))


def rank_mod_p(nrows, row_id, gen, vals):
    R = {}
    for r, g, x in zip(row_id.tolist(), gen.tolist(), vals.tolist()):
        if x:
            d = R.setdefault(r, {})
            nv = (d.get(g, 0) + x) % PR
            if nv:
                d[g] = nv
            else:
                d.pop(g, None)
    R = {r: d for r, d in R.items() if d}
    colrows = {}
    for r, d in R.items():
        for g in d:
            colrows.setdefault(g, set()).add(r)
    rank = 0
    while R:
        # Markowitz-style pivot: shortest row, sparsest column in it
        r = min(R, key=lambda r: len(R[r]))
        v = R.pop(r)
        for g in v:
            colrows[g].discard(r)
        j = min(v, key=lambda g: len(colrows.get(g, ())))
        inv = pow(v[j], PR - 2, PR)
        rank += 1
        for qq in list(colrows.get(j, ())):
            row = R[qq]
            f = row[j] * inv % PR
            for g, b in v.items():
                nv = (row.get(g, 0) - f * b) % PR
                if nv:
                    if g not in row:
                        colrows.setdefault(g, set()).add(qq)
                    row[g] = nv
                else:
                    if g in row:
                        del row[g]
                        colrows[g].discard(qq)
            if not row:
                del R[qq]
        colrows.pop(j, None)
    return rank


def sym_action(g):
    """10x10 matrix over Z/4 of Y -> g^-T Y g^-1 on UT coordinates."""
    gi = (-J @ g.T @ J) % 4
    cols = []
    for a, b in UT:
        E = np.zeros((4, 4), dtype=np.int64)
        E[a, b] = 1
        E[b, a] = 1
        Y = (gi.T @ E @ gi) % 4
        cols.append([Y[x, y] for x, y in UT])
    return np.array(cols, dtype=np.int64).T % 4       # y -> T y


def char_orbits():
    from scipy.sparse import coo_matrix
    from scipy.sparse.csgraph import connected_components
    N = 4 ** 10
    idx = np.arange(N, dtype=np.int64)
    F = np.stack([(idx // 4 ** k) % 4 for k in range(10)], axis=1)
    enc = 4 ** np.arange(10, dtype=np.int64)
    src, dst = [], []
    for i in range(1, 6):
        T = sym_action(B48.sigma_mat(i) % 4)
        # (g.f)(y) = f(T^-1 y): f -> f T^-1; T^-1 generates the same group as
        # T, so orbits of f -> f T coincide.
        img = ((F @ T) % 4) @ enc
        src.append(idx)
        dst.append(img)
    src = np.concatenate(src)
    dst = np.concatenate(dst)
    G = coo_matrix((np.ones(len(src), dtype=np.int8), (src, dst)),
                   shape=(N, N))
    ncomp, lab = connected_components(G, directed=True, connection="weak")
    reps = {}
    sizes = np.bincount(lab)
    for f in range(N):
        reps.setdefault(lab[f], f)
    orbits = []
    for comp, f in sorted(reps.items(), key=lambda t: t[1]):
        vec = [int(x) for x in F[f]]
        order = 1 if not any(vec) else (2 if all(x % 2 == 0 for x in vec)
                                        else 4)
        orbits.append({"f": vec, "size": int(sizes[comp]), "order": order})
    return orbits


_T = {}


def component(args):
    k, f = args
    t0 = time.time()
    nrows, row_id, gen, sgn, P4 = _T["terms"]
    e = (P4 @ np.array(f, dtype=np.int64)) % 4
    vals = (sgn * IPOW[e]) % PR
    rank = rank_mod_p(nrows, row_id, gen, vals)
    coker = len(L.GEN) - rank
    return k, {"coker_Fp": coker, "seconds": round(time.time() - t0, 1)}


if __name__ == "__main__":
    out = sys.argv[1]
    t0 = time.time()
    orbits = char_orbits()
    print("orbits:", len(orbits), "sizes by order:",
          {o: sorted(x["size"] for x in orbits if x["order"] == o)
           for o in (1, 2, 4)}, "total", sum(x["size"] for x in orbits),
          f"[{time.time()-t0:.1f}s]", flush=True)
    res = {"prime": PR, "orbits": orbits}
    if len(sys.argv) > 2 and sys.argv[2] == "orbits":
        json.dump(res, open(out, "w"), indent=1)
        raise SystemExit
    phi = schreier_images16()
    _T["terms"] = relator_terms(phi)
    print("relator rows", _T["terms"][0], "generators", len(L.GEN),
          f"[{time.time()-t0:.1f}s]", flush=True)
    import multiprocessing as mp
    nproc = int(os.environ.get("CHAR_PROCS", "1"))
    jobs = [(k, o["f"]) for k, o in enumerate(orbits)]
    with mp.get_context("fork").Pool(nproc) as pool:
        for k, c in pool.imap_unordered(component, jobs):
            orbits[k].update(c)
            o = orbits[k]
            b = c["coker_Fp"] - (0 if o["order"] == 1 else 1)
            o["b1_upper"] = b
            print(f"orbit {k} order {o['order']} size {o['size']}: "
                  f"coker_Fp {c['coker_Fp']} -> b_1^chi <= {b} "
                  f"[{c['seconds']}s]", flush=True)
            json.dump(res, open(out, "w"), indent=1)
    triv = [o for o in orbits if o["order"] == 1][0]
    res["b1_M16_upper"] = triv["b1_upper"] + sum(
        o["size"] * o["b1_upper"] for o in orbits if o["order"] > 1)
    res["b1_M8_upper"] = triv["b1_upper"] + sum(
        o["size"] * o["b1_upper"] for o in orbits if o["order"] == 2)
    print("b_1(M_8) <=", res["b1_M8_upper"], " b_1(M_16) <=",
          res["b1_M16_upper"], flush=True)
    res["seconds"] = round(time.time() - t0, 1)
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out)
