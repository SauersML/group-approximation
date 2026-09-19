#!/usr/bin/env python3
"""H_1 of level-(4 < G <= 8) subgroups as Z[K4/G]-modules (Shapiro + Fox).

K4 = Phi(Pbar) (512 cosets in Pbar = P_5/<Delta^2>) has the abelianised
Reidemeister-Schreier presentation of palindrome.py (4609 Schreier
generators, 18432 relator lifts).  For S <= sp_4(F_2) (see between48.py),
G = G_S <= K4 is normal with A = K4/G = sp_4(F_2)/S = F_2^q, q = codim S.
Each Schreier generator g_(c,p) = R_c A_p R_d^-1 maps to phi(c,p) in A
through its matrix mod 8, which is +-(I + 4X), X mod S.

Lifting every relator path to the A-cover gives the Fox matrix over Z[A];
its cokernel is H_1(Y, Y^0) = H_1(G) + Z^(|A|-1) (Y the A-cover of the
K4 presentation complex), and the classes of separating twists
(closed loops) lie in the summand H_1(G).  Unit pivots are eliminated over
Z[A] in the Walsh-Hadamard domain (Z[A] embeds in Z^|A| pointwise; its
units are exactly +-a, so "unit" means all character values are +-1).
The survivors are expanded to Z, then the census pipeline (integer unit
elimination, HNF, W, d, l1 certificate, minimal positive relation) runs.

    python3 groupring.py {gamma4|igusa48|randomK} out.json [seed]
"""
import json
import os
import random
import sys
import time
from math import gcd

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
import pure as P  # noqa: E402
import palindrome as L  # noqa: E402  (level-4 cosets, tree, Schreier gens)
import between48 as B48  # noqa: E402

NP = len(P.PAIRS)
J = C.J


def mat_inv_sp(M):
    """Inverse of a symplectic matrix (M^T J M = J), exact over Z."""
    return -J @ M.T @ J


def coset_mats(mats):
    R = []
    for c in range(len(L.ACT)):
        M = np.eye(4, dtype=np.int64)
        for a in L.REP[c]:
            M = (M @ mats[a - 1]) % 8
        R.append(M)
    return R


def make_label(S):
    """X (flattened 4x4 mod 2, X in sp_4(F_2)) -> index in A = sp/S."""
    S = [np.array(b) % 2 for b in S]
    piv = [int(np.nonzero(b)[0][0]) for b in S]
    basis = B48.sp4_f2_basis()

    def red(v):
        v = np.array(v) % 2
        for b, p in zip(S, piv):
            if v[p]:
                v = (v + b) % 2
        return tuple(int(t) for t in v)
    reps = {}
    for bits in np.ndindex(*([2] * 10)):
        v = sum(int(c) * b for c, b in zip(bits, basis)) % 2
        reps.setdefault(red(v), None)
    keys = sorted(reps)
    q = len(keys)
    assert q & (q - 1) == 0 and q == 2 ** (10 - len(S))
    zero = red(np.zeros(16, dtype=np.int64))
    # choose an F_2-linear labelling: greedy basis of the quotient
    lab = {zero: 0}
    gens = []
    for k in keys:
        if k in lab:
            continue
        gens.append(np.array(k))
        new = {}
        for kk, ii in lab.items():
            new[red(np.array(kk) + gens[-1])] = ii | (1 << (len(gens) - 1))
        lab.update(new)
    assert len(lab) == q

    def label(X):
        return lab[red(np.array(X).flatten())]
    return label, q


def schreier_images(S):
    mats = B48.pure_mats()
    R = coset_mats(mats)
    Rinv = [mat_inv_sp(M) % 8 for M in R]
    label, q = make_label(S)
    I = np.eye(4, dtype=np.int64)
    phi = {}
    for (c, p), g in L.GEN.items():
        d = L.ACT[c][p]
        M = (R[c] @ mats[p] @ Rinv[d]) % 8
        if ((M - I) % 4).any():
            M = (-M) % 8
            assert not ((M - I) % 4).any(), "Schreier element not in K4"
        X = ((M - I) // 4) % 2
        assert (((J % 2) @ X - ((J % 2) @ X).T) % 2 == 0).all()
        phi[(c, p)] = label(X)
    return phi, q


def fox_trace(word, c, phi, q):
    """Lift a pure word from coset c at A-position 0; return end coset,
    end position, and {schreier gen: std-basis vector over Z[A]}."""
    pos = 0
    vec = {}
    for a in word:
        p = abs(a) - 1
        if a > 0:
            g = L.GEN.get((c, p))
            if g is not None:
                v = vec.setdefault(g, np.zeros(q, dtype=np.int64))
                v[pos] += 1
                pos ^= phi[(c, p)]
            c = L.ACT[c][p]
        else:
            d = L.ACT[c][p]        # level-4 action is an involution (XOR)
            g = L.GEN.get((d, p))
            if g is not None:
                pos ^= phi[(d, p)]
                v = vec.setdefault(g, np.zeros(q, dtype=np.int64))
                v[pos] -= 1
            c = d
    return c, pos, vec


def wht_matrix(q):
    n = q.bit_length() - 1
    Hm = np.array([[(-1) ** bin(i & k).count("1") for k in range(q)]
                   for i in range(q)], dtype=np.int64)
    assert 2 ** n == q
    return Hm


def to_hat(vec, Hm):
    out = {}
    for g, v in vec.items():
        if v.any():
            out[g] = Hm @ v
    return out


def unit_eliminate_ring(rows, targets):
    """Unit-pivot elimination over Z[A] in the WHT domain."""
    rows = {r: v for r, v in enumerate(rows) if v}
    colrows = {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    tcol = {}
    for t, v in enumerate(targets):
        for g in v:
            tcol.setdefault(g, set()).add(t)
    progress = True
    npiv = 0
    while progress:
        progress = False
        for r in sorted(rows, key=lambda r: len(rows[r])):
            if r not in rows:
                continue
            v = rows[r]
            if not v:
                del rows[r]
                continue
            units = [g for g, a in v.items() if (np.abs(a) == 1).all()]
            if not units:
                continue
            j = min(units, key=lambda g: len(colrows.get(g, ())))
            s = v[j]
            piv = v
            del rows[r]
            for g in piv:
                colrows[g].discard(r)
            for store, index, keys in ((rows, colrows, list(colrows.get(j, ()))),
                                       (targets, tcol, list(tcol.get(j, ())))):
                for qq in keys:
                    row = store[qq]
                    f = row[j] * s
                    for g, b in piv.items():
                        nv = row.get(g)
                        nv = -f * b if nv is None else nv - f * b
                        if nv.any():
                            if g not in row:
                                index.setdefault(g, set()).add(qq)
                            row[g] = nv
                        elif g in row:
                            del row[g]
                            index[g].discard(qq)
                    assert j not in row
            colrows.pop(j, None)
            tcol.pop(j, None)
            npiv += 1
            progress = True
    big = max((int(np.abs(a).max()) for v in rows.values() for a in v.values()),
              default=0)
    assert big < 2 ** 40, "coefficient growth"
    cols = sorted({g for v in rows.values() for g in v} |
                  {g for v in targets for g in v})
    return cols, list(rows.values()), targets, npiv


def expand(vec_hat, cols, Hm, q):
    """Z[A]-row (WHT domain) -> q integer rows (all A-translates), as dicts
    over integer columns col_index * q + k."""
    ci = {g: i for i, g in enumerate(cols)}
    std = {}
    for g, a in vec_hat.items():
        x = Hm @ a
        assert (x % q == 0).all()
        std[g] = x // q
    out = []
    for t in range(q):
        d = {}
        for g, x in std.items():
            base = ci[g] * q
            for k in range(q):
                val = int(x[k ^ t])
                if val:
                    d[base + k] = val
        out.append(d)
    return out


def run(S, label, milp=True):
    t0 = time.time()
    phi, q = schreier_images(S)
    Hm = wht_matrix(q)
    rels = [(u, v) for u, v in P.check_presentation()]
    rels.append((P.delta2_pure(), ()))
    rows = []
    for u, v in rels:
        w = tuple(u) + P.finv(v)
        for c in range(len(L.ACT)):
            d, pos, vec = fox_trace(w, c, phi, q)
            assert d == c and pos == 0, "relator does not close in A-cover"
            vh = to_hat(vec, Hm)
            if vh:
                rows.append(vh)
    tab = P.conj_table()
    TW = P.standard_twists(tab)
    targets, owner = [], []
    for ti, t in enumerate(P.TRIPLES):
        sq = TW[t] * 2
        for c in range(len(L.ACT)):
            d, pos, vec = fox_trace(sq, c, phi, q)
            assert d == c and pos == 0, "twist square not in G"
            targets.append(to_hat(vec, Hm))
            owner.append(ti)
    print(f"[{label}] |A| = {q}, ring rows {len(rows)} [{time.time()-t0:.1f}s]",
          flush=True)
    cols, R, T, npiv = unit_eliminate_ring(rows, targets)
    del rows
    print(f"[{label}] ring elimination: {npiv} pivots, {len(cols)} ring cols, "
          f"{len(R)} ring rows [{time.time()-t0:.1f}s]", flush=True)
    ncol = len(cols) * q
    Hcur = []
    chunk = []
    nrows_int = 0

    def flush(Hcur, chunk):
        from flint import fmpz_mat
        M = fmpz_mat(Hcur + chunk) if (Hcur or chunk) else None
        if M is None:
            return []
        Hn = M.hnf()
        out = []
        for i in range(Hn.nrows()):
            r = [int(Hn[i, j]) for j in range(ncol)]
            if any(r):
                out.append(r)
        return out
    seen = set()
    for v in R:
        for d in expand(v, cols, Hm, q):
            key = tuple(sorted(d.items()))
            if not d or key in seen:
                continue
            seen.add(key)
            row = [0] * ncol
            for kk, a in d.items():
                row[kk] = a
            chunk.append(row)
            nrows_int += 1
            if len(chunk) >= max(2000, ncol):
                Hcur = flush(Hcur, chunk)
                chunk = []
    Hcur = flush(Hcur, chunk)
    del seen, R
    H = Hcur
    n = ncol
    print(f"[{label}] integer: {n} cols, {nrows_int} distinct rows, "
          f"HNF rank {len(H)} [{time.time()-t0:.1f}s]", flush=True)
    rank_rel, tors = C.h1_invariants(H, n)
    rank = rank_rel - (q - 1)
    print(f"[{label}] H_1(G) = Z^{rank} + {tors} [{time.time()-t0:.1f}s]",
          flush=True)
    # distinct targets (up to exact equality), with all A-translates
    uniq = {}
    for v, o in zip(T, owner):
        for d in expand(v, cols, Hm, q):
            uniq.setdefault(tuple(sorted(d.items())), o)
    tk = list(uniq)
    X = np.zeros((len(tk), n), dtype=object)
    for i, key in enumerate(tk):
        for kk, a in key:
            X[i, kk] = a
    for r in H:
        p = next(j for j, a in enumerate(r) if a)
        rr = np.array(r, dtype=object)
        qv = X[:, p] // r[p]
        nzq = np.nonzero(qv)[0]
        if len(nzq):
            X[nzq] -= np.outer(qv[nzq], rr)
    classes = {}
    for i in range(len(tk)):
        classes.setdefault(tuple(int(t) for t in X[i]), uniq[tk[i]])
    del X
    keys = sorted(classes)
    per = {}
    for kk in keys:
        per[classes[kk]] = per.get(classes[kk], 0) + 1
    print(f"[{label}] {len(tk)} distinct target vectors, {len(keys)} classes "
          f"[{time.time()-t0:.1f}s]", flush=True)
    Bw = C.w_lattice(H, [list(x) for x in keys], n)
    g = 0
    for r in Bw:
        g = gcd(g, sum(r))
    res = {"label": label, "codim_S_in_sp4F2": 10 - len(S), "A_order": q,
           "cosets_in_Pbar": 512 * q, "h1_rank": rank, "h1_torsion": tors,
           "classes": len(keys),
           "classes_per_splitting": sorted(set(per.values())),
           "W_rank": len(Bw), "gcd_aug": g}
    print(res, f"[{time.time()-t0:.1f}s]", flush=True)
    if milp and Bw:
        dist = C.distance_milp(Bw)
        if dist is not None:
            res["d"] = str(dist[0])
        l1, _ = C.best_certificate(Bw)
        res["signed_cert_l1"] = l1
        for rm in (1, 2):
            s, w = B48.positive_min(Bw, rm)
            if s is not None:
                res[f"positive_min_aug_{rm}mod3"] = s
                res[f"positive_min_aug_{rm}mod3_support"] = sum(
                    1 for a in w if a)
                res[f"positive_min_aug_{rm}mod3_splittings"] = sorted(
                    {classes[keys[j]] for j, a in enumerate(w) if a})
        print(res, f"[{time.time()-t0:.1f}s]", flush=True)
    res["seconds"] = round(time.time() - t0, 1)
    return res


if __name__ == "__main__":
    which = sys.argv[1]
    out = sys.argv[2]
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    if which == "gamma4":
        S = [np.array(b) for b in B48.sp4_f2_basis()]
    elif which == "igusa48":
        S = [np.array(b) for b in B48.alt_subspace()]
    elif which.startswith("random"):
        S = B48.random_S(int(which[6:]), rng)
    res = run(S, which)
    if len(sys.argv) > 3:
        res["seed"] = int(sys.argv[3])
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out)
