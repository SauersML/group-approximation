#!/usr/bin/env python3
"""Exact separating-twist census for K8 <= G_S <= K4 by character splitting.

Setting of groupring.py: A = K4/G = F_2^q, and the Fox matrix of the
512-coset presentation of K4 over Z[A] presents H_1(Y, Y^0) = H_1(G) + Z^(q-1).
Over Z[1/2], Z[A] = Z[1/2]^q (idempotents), so

    H_1(G)[1/2] = (+)_chi  H_1(K4; Z[1/2]_chi),

and each summand is a level-four-sized sign-twisted Reidemeister-Schreier
computation M_chi (entries = character values of the Fox entries).  The class
of the conjugate of t_s by (a, c) has chi-component chi(a) u^chi_(c,t).

Exactness at 2.  dim_F2 H_1(G; F_2) is computed separately over the local
ring F_2[A] (units = odd-weight elements, u^-1 = u since x^2 = aug(x)).
If it equals rank_Z H_1(G) and no coker M_chi has torsion, then H_1(G) is
torsion-free, H_1(G) -> H_1(G)[1/2] is injective and every rowspace is
saturated, so the classes and W computed here are the exact integral ones.

    python3 characters.py {gamma4|igusa48|randomK|sp4orbitK} out.json [seed]
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
import palindrome as L  # noqa: E402
import between48 as B48  # noqa: E402
import groupring as GR  # noqa: E402

NP = len(P.PAIRS)


def lifts(S):
    phi, q = GR.schreier_images(S)
    rels = [(u, v) for u, v in P.check_presentation()]
    rels.append((P.delta2_pure(), ()))
    rows = []
    for u, v in rels:
        w = tuple(u) + P.finv(v)
        for c in range(len(L.ACT)):
            d, pos, vec = GR.fox_trace(w, c, phi, q)
            assert d == c and pos == 0, "relator does not close in A-cover"
            vec = {g: x for g, x in vec.items() if x.any()}
            if vec:
                rows.append(vec)
    TW = P.standard_twists(P.conj_table())
    targets, owner = [], []
    for ti, t in enumerate(P.TRIPLES):
        sq = TW[t] * 2
        for c in range(len(L.ACT)):
            d, pos, vec = GR.fox_trace(sq, c, phi, q)
            assert d == c and pos == 0, "twist square not in G"
            targets.append({g: x for g, x in vec.items() if x.any()})
            owner.append(ti)
    return q, rows, targets, owner


# ------------------------------------------------------------ Z[1/2] part
def char_component(vecs, Hm, k):
    out = []
    for vec in vecs:
        d = {}
        for g, x in vec.items():
            val = int(Hm[k] @ x)
            if val:
                d[g] = val
        out.append(d)
    return out


def twisted(rows, targets, Hm, k):
    ngen = len(L.GEN)
    Rk = char_component(rows, Hm, k)
    Tk = char_component(targets, Hm, k)
    cols, R, V = C.unit_eliminate(ngen, [r for r in Rk if r], Tk)
    n = len(cols)
    Rd = sorted({tuple(r) for r in C.to_dense(R, cols)})
    H = C.hnf_rows([list(r) for r in Rd], n)
    rank, tors = C.h1_invariants(H, n)
    odd = [t for t in tors if t & (t - 1)]
    if os.environ.get("CHAR_RANKS_ONLY"):
        return {"n": n, "H": H, "rank": rank, "tors": tors, "odd": odd,
                "red": None}
    Vd = C.to_dense(V, cols)
    red_p = [C.reduce_mod_hnf(v, H) for v in Vd]
    red_m = [C.reduce_mod_hnf([-a for a in v], H) for v in Vd]
    return {"n": n, "H": H, "rank": rank, "tors": tors, "odd": odd,
            "red": (red_p, red_m)}


_JOB = {}


def _twisted_job(k):
    c = twisted(_JOB["rows"], _JOB["targets"], _JOB["Hm"], k)
    return k, c


# ------------------------------------------------------------ F_2[A] part
def f2_dimension(rows, q):
    """dim_F2 H_1(Y, Y^0; F_2) by elimination over the local ring F_2[A]."""
    Q = 1 << q
    perm = [[0] * (1 << Q) for _ in range(Q)]
    for i in range(Q):
        for m in range(1 << Q):
            out = 0
            mm = m
            while mm:
                b = (mm & -mm).bit_length() - 1
                out |= 1 << (b ^ i)
                mm &= mm - 1
            perm[i][m] = out

    def mul(a, b):
        out = 0
        while a:
            i = (a & -a).bit_length() - 1
            out ^= perm[i][b]
            a &= a - 1
        return out

    def mask(x):
        m = 0
        for i, v in enumerate(x):
            if v % 2:
                m |= 1 << i
        return m
    R = {}
    for r, vec in enumerate(rows):
        d = {g: mask(x) for g, x in vec.items()}
        d = {g: m for g, m in d.items() if m}
        if d:
            R[r] = d
    colrows = {}
    for r, v in R.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    alive = set(range(len(L.GEN)))
    progress = True
    while progress:
        progress = False
        for r in sorted(R, key=lambda r: len(R[r])):
            if r not in R:
                continue
            v = R[r]
            if not v:
                del R[r]
                continue
            units = [g for g, m in v.items() if bin(m).count("1") % 2]
            if not units:
                continue
            j = min(units, key=lambda g: len(colrows.get(g, ())))
            s = v[j]
            del R[r]
            for g in v:
                colrows[g].discard(r)
            for qq in list(colrows.get(j, ())):
                row = R[qq]
                f = mul(row[j], s)
                for g, b in v.items():
                    nv = row.get(g, 0) ^ mul(f, b)
                    if nv:
                        if g not in row:
                            colrows.setdefault(g, set()).add(qq)
                        row[g] = nv
                    elif g in row:
                        del row[g]
                        colrows[g].discard(qq)
            colrows.pop(j, None)
            alive.discard(j)
            progress = True
    cols = sorted(alive)
    ci = {g: i for i, g in enumerate(cols)}
    # expand to F_2 (all A-translates) and take the rank with int bitsets
    piv = {}
    rank = 0
    for v in R.values():
        for t in range(Q):
            x = 0
            for g, m in v.items():
                mt = perm[t][m]
                x |= mt << (ci[g] * Q)
            while x:
                h = x.bit_length() - 1
                if h in piv:
                    x ^= piv[h]
                else:
                    piv[h] = x
                    rank += 1
                    break
    return Q * len(cols) - rank, len(cols)


# ------------------------------------------------------------------- main
def run(S, label, milp=True):
    t0 = time.time()
    qbits = 10 - len(S)
    q, rows, targets, owner = lifts(S)
    assert q == 1 << qbits
    Hm = GR.wht_matrix(q)
    print(f"[{label}] |A| = {q}, lifts done [{time.time()-t0:.1f}s]",
          flush=True)
    # F_2 dimension first (cheap, single process)
    f2rel, f2cols = f2_dimension(rows, qbits)
    f2 = f2rel - (q - 1)
    print(f"[{label}] dim H_1(G;F_2) = {f2} (F_2[A] survivors {f2cols}) "
          f"[{time.time()-t0:.1f}s]", flush=True)
    comps = [None] * q
    nproc = int(os.environ.get("CHAR_PROCS", "1"))
    ks = [int(x) for x in os.environ["CHAR_KS"].split(",")] \
        if os.environ.get("CHAR_KS") else list(range(q))
    _JOB.update(rows=rows, targets=targets, Hm=Hm)

    def report(k, c):
        comps[k] = c
        print(f"[{label}] chi {k}: {c['n']} cols, coker Z^{c['rank']} + "
              f"{dict((str(t), c['tors'].count(t)) for t in set(c['tors']))}"
              f" odd={c['odd']} [{time.time()-t0:.1f}s]", flush=True)
    if nproc > 1:
        import multiprocessing as mp
        with mp.get_context("fork").Pool(nproc) as pool:
            for k, c in pool.imap_unordered(_twisted_job, ks):
                report(k, c)
    else:
        for k in ks:
            report(*_twisted_job(k))
    if any(c is None for c in comps):
        res = {"label": label, "partial_chi": ks, "h1_F2_dim": f2,
               "chi_coker_ranks": {k: comps[k]["rank"] for k in ks},
               "chi_torsion": {k: {str(t): comps[k]["tors"].count(t)
                                   for t in set(comps[k]["tors"])}
                               for k in ks},
               "chi_odd_torsion": {k: comps[k]["odd"] for k in ks}}
        print(res, flush=True)
        return res
    rank = comps[0]["rank"] + sum(c["rank"] - 1 for c in comps[1:])
    odd_any = any(c["odd"] for c in comps)
    # H_1(G)[1/2] = (+) coker M_chi [1/2] has no torsion iff no odd torsion;
    # then torsion of H_1(G) is 2-primary and vanishes iff dim_F2 = rank.
    exact = (f2 == rank) and not odd_any
    print(f"[{label}] rank H_1(G) = {rank}, dim H_1(G;F_2) = {f2}, "
          f"odd torsion = {odd_any}; torsion-free = {exact} "
          f"[{time.time()-t0:.1f}s]", flush=True)
    if os.environ.get("CHAR_RANKS_ONLY"):
        return {"label": label, "codim_S_in_sp4F2": qbits, "A_order": q,
                "cosets_in_Pbar": 512 * q, "h1_rank": rank,
                "h1_F2_dim": f2, "odd_torsion": odd_any,
                "h1_torsion_free": exact,
                "chi_coker_ranks": [c["rank"] for c in comps],
                "chi_cols": [c["n"] for c in comps],
                "chi_torsion": [{str(t): c["tors"].count(t)
                                 for t in set(c["tors"])} for c in comps],
                "seconds": round(time.time() - t0, 1)}
    # classes: (a, c, t) -> tuple over chi of reduced chi(a) u^chi_(c,t)
    classes = {}
    for a in range(q):
        for i, o in enumerate(owner):
            key = tuple(comps[k]["red"][0 if Hm[k, a] > 0 else 1][i]
                        for k in range(q))
            classes.setdefault(key, o)
    keys = sorted(classes)
    per = {}
    for kk in keys:
        per[classes[kk]] = per.get(classes[kk], 0) + 1
    # W = {w : sum_j w_j x_j = 0 in every chi-component}
    ntot = sum(c["n"] for c in comps)
    offs = np.cumsum([0] + [c["n"] for c in comps])
    Hblock = []
    for k, c in enumerate(comps):
        for r in c["H"]:
            row = [0] * ntot
            row[offs[k]:offs[k] + c["n"]] = r
            Hblock.append(row)
    V = [[x for k in range(q) for x in kk[k]] for kk in keys]
    Bw = C.w_lattice(Hblock, V, ntot)
    g = 0
    for r in Bw:
        g = gcd(g, sum(r))
    res = {"label": label, "codim_S_in_sp4F2": qbits, "A_order": q,
           "cosets_in_Pbar": 512 * q, "h1_rank": rank,
           "h1_F2_dim": f2, "chi_torsion": [c["tors"] for c in comps],
           "chi_coker_ranks": [c["rank"] for c in comps],
           "exact_integral": exact, "classes": len(keys),
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
                res[f"positive_min_aug_{rm}mod3_multiplicities"] = sorted(
                    {a for a in w if a})
        print(res, f"[{time.time()-t0:.1f}s]", flush=True)
    res["seconds"] = round(time.time() - t0, 1)
    return res


def sp4_orbit_S(codim, rng):
    """A random S of the given codimension (alias of between48.random_S)."""
    return B48.random_S(codim, rng)


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
    else:
        raise SystemExit("unknown subgroup " + which)
    res = run(S, which)
    if len(sys.argv) > 3:
        res["seed"] = int(sys.argv[3])
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out)
