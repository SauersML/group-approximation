#!/usr/bin/env python3
"""Exact integral separating-twist census at the Igusa level Gamma(4,8).

G = pi^-1(Gamma(4,8)) inside Pbar = PMod(S_{0,6}) (Birman-Hilden; the
hyperelliptic involution is not in Gamma(4), so G is the Torelli preimage).
8192 cosets in Pbar.  Pipeline (reuses the landed toolkit of
experiments/mod-s2-palindrome-transversal-relations-2026-09-17):

  1. Reidemeister-Schreier presentation of H_1(G) (abelianised), with the
     classes v of the squares of the ten standard 3-point twists at every
     coset (these are the images of the separating twists t_s, s over each
     level-two splitting, conjugated by every coset representative).
  2. Exact Z-elimination of generators with a +-1 coefficient.
  3. The surviving relation matrix R (n columns) is reduced modulo 2^m
     (m = 12 > 4 >= k, so Z/2^m sees the whole 2-primary torsion, which is
     cyclic of order 2^k, k <= 4) and over Q (rank).  Odd torsion is absent
     (igusa48-results.json), so H_1(G) (x) Z_(2) is determined by R mod 2^m
     together with the rank.
  4. Every class v is reduced to a normal form in (Z/2^m)^n / R, which
     determines the class in H_1(G) (x) Z/2^m = Z/2^m^54 + Z/2^k.  Since
     H_1(G) = Z^54 + Z/2^k has no odd torsion and the free part injects
     into H_1(G)/2^m, two classes agree in H_1(G) iff they agree mod 2^m
     AND ... (see check in step 5).

    python3 igusa_exact.py stage1 out.pkl     (RS + unit elimination)
"""
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(HERE, "..", "mod-s2-palindrome-transversal-relations-2026-09-17")
sys.path.insert(0, TOOL)
sys.path.insert(0, os.path.join(HERE, "..", "mod-s2-torelli-scalar-census-2026-09-17"))
import numpy as np  # noqa: E402
import census as C  # noqa: E402
import pure as P  # noqa: E402
import between48 as B48  # noqa: E402


def stage1(out):
    t0 = time.time()
    S = [np.array(b) for b in B48.alt_subspace()]
    act = B48.enumerate_cosets(S)
    k = len(act)
    gen = B48.schreier(act)
    rels = [(u, v) for u, v in P.check_presentation()]
    rels.append((P.delta2_pure(), ()))
    rows = []
    for u, v in rels:
        w = tuple(u) + P.finv(v)
        for c in range(k):
            vec = {}
            assert B48.trace(act, gen, w, c, vec) == c
            vec = {g: a for g, a in vec.items() if a}
            if vec:
                rows.append(vec)
    tab = P.conj_table()
    TW = P.standard_twists(tab)
    vs, owner = [], []
    for ti, t in enumerate(P.TRIPLES):
        sq = TW[t] * 2
        for c in range(k):
            vec = {}
            assert B48.trace(act, gen, sq, c, vec) == c
            vs.append({g: a for g, a in vec.items() if a})
            owner.append((ti, c))
    print(f"cosets {k}, gens {len(gen)}, relators {len(rows)} "
          f"[{time.time()-t0:.1f}s]", flush=True)
    cols, R, V = C.unit_eliminate(len(gen), rows, vs)
    print(f"surviving cols {len(cols)}, rows {len(R)} [{time.time()-t0:.1f}s]",
          flush=True)
    with open(out, "wb") as f:
        pickle.dump({"cols": cols, "R": R, "V": V, "owner": owner,
                     "k": k, "act": act}, f)


def rs_vectors(S):
    """RS presentation for G_S (S subspace of sp4(F_2)); returns act, gen,
    relator rows and the class vectors of the ten twist squares at every
    coset, owner[i] = (triple index, coset)."""
    act = B48.enumerate_cosets(S)
    k = len(act)
    gen = B48.schreier(act)
    rels = [(u, v) for u, v in P.check_presentation()]
    rels.append((P.delta2_pure(), ()))
    rows = []
    for u, v in rels:
        w = tuple(u) + P.finv(v)
        for c in range(k):
            vec = {}
            assert B48.trace(act, gen, w, c, vec) == c
            vec = {g: a for g, a in vec.items() if a}
            if vec:
                rows.append(vec)
    tab = P.conj_table()
    TW = P.standard_twists(tab)
    vs, owner = [], []
    for ti, t in enumerate(P.TRIPLES):
        sq = TW[t] * 2
        for c in range(k):
            vec = {}
            assert B48.trace(act, gen, sq, c, vec) == c
            vs.append({g: a for g, a in vec.items() if a})
            owner.append((ti, c))
    return act, gen, rows, vs, owner


def level4(out):
    """Exact H_1(K4) = H_1(M_4) and the level-4 class key of every
    (triple, level-4 coset); keys are HNF normal forms, W_4 its relation
    lattice.  Also stores the coset keys (M mod 4 up to sign) so that
    Igusa cosets can be mapped to level-4 cosets."""
    t0 = time.time()
    S = [np.array(b) for b in B48.sp4_f2_basis()]
    act, gen, rows, vs, owner = rs_vectors(S)
    cols, R, V = C.unit_eliminate(len(gen), rows, vs)
    n = len(cols)
    Rd = sorted({tuple(r) for r in C.to_dense(R, cols)})
    H = C.hnf_rows([list(r) for r in Rd], n)
    rank, tors = C.h1_invariants(H, n)
    Vd = C.to_dense(V, cols)
    keys = [C.reduce_mod_hnf(v, H) for v in Vd]
    distinct = sorted(set(keys))
    kidx = {kk: i for i, kk in enumerate(distinct)}
    lab = [kidx[kk] for kk in keys]
    B4 = C.w_lattice(H, [list(x) for x in distinct], n)
    print(f"level4: cosets {len(act)}, H_1 = Z^{rank} + {tors}, "
          f"classes {len(distinct)}, W rank {len(B4)} [{time.time()-t0:.1f}s]",
          flush=True)
    with open(out, "wb") as f:
        pickle.dump({"lab": lab, "owner": owner, "B4": B4, "n4": n, "act": act,
                     "distinct": distinct, "H": H, "rank": rank,
                     "tors": tors}, f)


def hnf_chunked(rows, n, chunk=4000):
    """Exact HNF of the row module of `rows` (dense int lists), in chunks."""
    H = []
    for i in range(0, len(rows), chunk):
        H = C.hnf_rows(H + [list(r) for r in rows[i:i + chunk]], n)
        print(f"  hnf {min(i + chunk, len(rows))}/{len(rows)}: {len(H)} rows",
              flush=True)
    return H


def coset_map(actI, act4):
    """phi: Igusa cosets -> level-4 cosets, phi(0) = 0, phi(c.p) = phi(c).p."""
    phi = [None] * len(actI)
    phi[0] = 0
    queue = [0]
    for c in queue:
        for p, d in enumerate(actI[c]):
            e = act4[phi[c]][p]
            if phi[d] is None:
                phi[d] = e
                queue.append(d)
            else:
                assert phi[d] == e
    return phi


def stage2(s1file, l4file, out):
    import json
    t0 = time.time()
    s1 = pickle.load(open(s1file, "rb"))
    l4 = pickle.load(open(l4file, "rb"))
    cols, R, V, owner = s1["cols"], s1["R"], s1["V"], s1["owner"]
    n = len(cols)
    Rd = sorted({tuple(r) for r in C.to_dense(R, cols)})
    print(f"stage2: n {n}, distinct rows {len(Rd)}", flush=True)
    H = hnf_chunked(Rd, n)
    rank, tors = C.h1_invariants(H, n)
    print(f"H_1(Igusa preimage) = Z^{rank} + {tors} [{time.time()-t0:.1f}s]",
          flush=True)
    keys = [C.reduce_mod_hnf(v, H) for v in C.to_dense(V, cols)]
    distinct = sorted(set(keys))
    kidx = {kk: i for i, kk in enumerate(distinct)}
    lab = [kidx[kk] for kk in keys]
    # level-4 label of every Igusa vector, through the covering of cosets
    phi = coset_map(s1["act"], l4["act"])
    k4 = len(l4["act"])
    assert all(l4["owner"][ti * k4 + c] == (ti, c) for ti in range(10)
               for c in range(k4))
    down = {}
    for i, (ti, c) in enumerate(owner):
        d4 = l4["lab"][ti * k4 + phi[c]]
        assert down.setdefault(lab[i], d4) == d4, "class not over one class"
    m = len(distinct)
    fib = {}
    for a, b in down.items():
        fib.setdefault(b, []).append(a)
    print(f"classes {m} over {len(fib)} level-4 classes, fibre sizes "
          f"{sorted({len(v) for v in fib.values()})}", flush=True)
    B = C.w_lattice(H, [list(x) for x in distinct], n)
    print(f"W rank {len(B)} [{time.time()-t0:.1f}s]", flush=True)
    res = {"cosets": s1["k"], "surviving_cols": n, "b1": rank,
           "torsion": tors, "classes": m, "level4_classes": len(fib),
           "fibre_sizes": sorted({len(v) for v in fib.values()}),
           "W_rank": len(B)}
    json.dump(res, open(out, "w"), indent=1)
    pickle.dump({"B": B, "down": down, "lab": lab, "B4": l4["B4"]},
                open(out + ".pkl", "wb"))
    print(json.dumps(res), flush=True)


def stage3(resfile, out):
    """Census of W: exact d, best l1 certificate, positive minima."""
    import json
    t0 = time.time()
    res = json.load(open(resfile))
    B = pickle.load(open(resfile + ".pkl", "rb"))["B"]
    dev, h = C.distance_milp(B)
    res["d"] = str(dev)
    print(f"d = {dev} [{time.time()-t0:.1f}s]", flush=True)
    l1, w = C.best_certificate(B)
    res["best_l1_certificate"] = l1
    print(f"best l1 certificate {l1} [{time.time()-t0:.1f}s]", flush=True)
    for r in (1, 2):
        a, wp = B48.positive_min(B, r)
        res[f"positive_min_aug_{r}_mod_3"] = a
        if wp is not None:
            res[f"positive_min_aug_{r}_support"] = {
                str(j): x for j, x in enumerate(wp) if x}
        print(f"positive min (aug {r} mod 3) = {a} [{time.time()-t0:.1f}s]",
              flush=True)
    res["optimal_character_h"] = h
    json.dump(res, open(out, "w"), indent=1)


if __name__ == "__main__":
    if sys.argv[1] == "stage1":
        stage1(sys.argv[2])
    elif sys.argv[1] == "level4":
        level4(sys.argv[2])
    elif sys.argv[1] == "stage2":
        stage2(sys.argv[2], sys.argv[3], sys.argv[4])
    elif sys.argv[1] == "stage3":
        stage3(sys.argv[2], sys.argv[3])
