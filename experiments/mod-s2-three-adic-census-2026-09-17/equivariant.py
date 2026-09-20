#!/usr/bin/env python3
"""Exact H_1(M_Y) and Torelli census of M_Y = pi^{-1}(G_Y), Z/3-equivariantly.

The direct Reidemeister-Schreier elimination on the 77760 cosets of
M_Y<iota> in Pbar = M/<iota> runs out of memory (fill).  Instead:
  * D = deck transformation (gbar, c) -> (gbar, c + 1) of the 3-sheeted
    cover of the Gamma(3)-level coset graph (25920 cosets of M_3<iota>);
  * base cosets B = D-orbits, each with a representative q_B chosen along a
    BFS tree so that tree edges have sheet label 0;
  * cellular chains of the (tree-contracted) cover are free over
    R = Z[Z/3] = Z[t]/(t^3 - 1):  C_2 = R^rels -> C_1 = R^gens -> C_0 = R^1,
    the Fox matrix having entries in R (t^sheet at each Schreier letter);
  * (2-cell, 1-cell) pairs are collapsed equivariantly through entries
    +-t^e (trivial units): each step is 3 elementary collapses of the
    cover and preserves homology;
  * the survivor is expanded to Z (R = Z^3 with the regular action) and
    handed to census.py's HNF / W / MILP code.
Q = C_1 / im d_2 = H_1(M_Y) + d_1(C_1), and d_1(C_1) = augmentation ideal
of Z[Z/3] (free of rank 2) because the cover is connected (Y != 0).  So
tors Q = tors H_1(M_Y), rank Q = b_1(M_Y) + 2, and the twist classes (closed
loops, in ker d_1 = H_1 part) have the same relation lattice W in Q.

Usage: python3 equivariant.py <orbit index> ...     ('flat<a>' = check mode:
sheet labels forced to 0, i.e. the trivial cover; expect H_1(M_3)^3, rank 72.)
"""
import json
import os
import sys
import time

import threeadic
from threeadic import census, log

HERE = os.path.dirname(os.path.abspath(__file__))
NA = 3


def rmul(x, y):
    return tuple(sum(x[i] * y[(k - i) % NA] for i in range(NA)) for k in range(NA))


def rsub_mul(a, f, b):
    """a - f*b in R."""
    fb = rmul(f, b)
    return tuple(a[k] - fb[k] for k in range(NA))


def is_zero(x):
    return not any(x)


def unit_inverse(x):
    """x = +-t^e -> x^{-1} = +-t^{-e}; else None."""
    nz = [(k, a) for k, a in enumerate(x) if a]
    if len(nz) != 1 or nz[0][1] not in (1, -1):
        return None
    k, a = nz[0]
    out = [0] * NA
    out[(-k) % NA] = a
    return tuple(out)


def mono(e):
    out = [0] * NA
    out[e % NA] = 1
    return tuple(out)


ORIG_RELATORS = census.relators


def cover_tables(Y):
    """Quotient table of M_Y<iota> (77760 cosets), deck map, and the base
    (Gamma(3)-level, 25920 cosets) table with sheet labels."""
    act, lift = threeadic.coset_table(Y)
    census.relators = ORIG_RELATORS
    census.check_action(act)
    k0 = len(act)
    iota = [census.trace_perm(act, c, census.IOTA) for c in range(k0)]
    qact, orig = threeadic.quotient_table(act)
    census.relators = threeadic.relators_mod_iota
    census.check_action(qact)
    k = len(qact)
    new = {r: q for q, r in enumerate(orig)}

    def deck(q):
        o = orig[q]
        o2 = 3 * (o // 3) + (o % 3 + 1) % 3
        return new[min(o2, iota[o2])]
    D = [deck(q) for q in range(k)]
    for q in range(k):
        assert all(D[qact[q][i]] == qact[D[q]][i] for i in range(census.NGEN))
    assert all(D[q] != q and D[D[D[q]]] == q for q in range(k))
    # base cosets and gauge along a BFS tree (tree edges get label 0)
    base_of, sheet, reps = [-1] * k, [0] * k, []

    def new_base(q):
        b = len(reps)
        reps.append(q)
        x = q
        for s in range(NA):
            assert base_of[x] < 0
            base_of[x], sheet[x] = b, s
            x = D[x]
        assert x == q
        return b
    new_base(0)
    tree = set()
    for b in range(10 ** 9):
        if b >= len(reps):
            break
        for i in range(census.NGEN):
            q2 = qact[reps[b]][i]
            if base_of[q2] < 0:
                new_base(q2)
                tree.add((b, i))
    nb = len(reps)
    bact = [[base_of[qact[reps[b]][i]] for i in range(census.NGEN)]
            for b in range(nb)]
    lab = [[sheet[qact[reps[b]][i]] for i in range(census.NGEN)]
           for b in range(nb)]
    assert all(lab[b][i] == 0 for (b, i) in tree)
    return dict(qact=qact, orig=orig, lift=lift, D=D, reps=reps,
                base_of=base_of, sheet=sheet, bact=bact, lab=lab, tree=tree)


def trace_r(T, gen, b, word, vec, sgn):
    """Trace word from (base b, sheet 0); add sgn * t^sheet at each Schreier
    letter into vec.  Returns (end base, end sheet)."""
    bact, lab = T["bact"], T["lab"]
    s = 0
    for letter in word:
        g = gen.get((b, letter))
        if g is not None:
            old = vec.get(g, (0,) * NA)
            e = list(old)
            e[s] += sgn
            vec[g] = tuple(e)
        s = (s + lab[b][letter]) % NA
        b = bact[b][letter]
    return b, s


def fox_data(T):
    nb = len(T["reps"])
    gen = {}
    for b in range(nb):
        for i in range(census.NGEN):
            if (b, i) not in T["tree"]:
                gen[(b, i)] = len(gen)
    rels = []
    for u, v in threeadic.relators_mod_iota():
        for b in range(nb):
            vec = {}
            e1 = trace_r(T, gen, b, u, vec, 1)
            e2 = trace_r(T, gen, b, v, vec, -1)
            assert e1 == e2
            vec = {g: a for g, a in vec.items() if any(a)}
            if vec:
                rels.append(vec)
    return gen, rels


def twist_vectors(T, gen, bases):
    out = []
    for b in bases:
        vec = {}
        e = trace_r(T, gen, b, census.T_S, vec, 1)
        assert e == (b, 0)          # T_S lies in K <= M_Y: closed on sheet 0
        out.append({g: a for g, a in vec.items() if any(a)})
    return out


def eliminate_r(ngen, rels, vs):
    """census.unit_eliminate over R = Z[Z/3], pivots +-t^e."""
    rows = {r: v for r, v in enumerate(rels)}
    colrows = {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    vrows = [dict(v) for v in vs]
    vcol = {}
    for t, v in enumerate(vrows):
        for g in v:
            vcol.setdefault(g, set()).add(t)
    alive = set(range(ngen))

    def reduce(row, rid, cmap, j, pinv, piv):
        f = rmul(row[j], pinv)
        for g, b in piv.items():
            nv = rsub_mul(row.get(g, (0,) * NA), f, b)
            if any(nv):
                if g not in row:
                    cmap.setdefault(g, set()).add(rid)
                row[g] = nv
            elif g in row:
                del row[g]
                cmap[g].discard(rid)
    progress, npass = True, 0
    while progress:
        progress = False
        npass += 1
        for r in sorted(rows, key=lambda r: len(rows[r])):
            if r not in rows:
                continue
            v = rows[r]
            if not v:
                del rows[r]
                continue
            units = [g for g, a in v.items() if unit_inverse(a) is not None]
            if not units:
                continue
            j = min(units, key=lambda g: len(colrows.get(g, ())))
            pinv = unit_inverse(v[j])
            piv = v
            del rows[r]
            for g in piv:
                colrows[g].discard(r)
            for q in list(colrows.get(j, ())):
                reduce(rows[q], q, colrows, j, pinv, piv)
                if not rows[q]:
                    del rows[q]
            for t in list(vcol.get(j, ())):
                reduce(vrows[t], t, vcol, j, pinv, piv)
            alive.discard(j)
            colrows.pop(j, None)
            vcol.pop(j, None)
            progress = True
        log(f"pass {npass}: {len(alive)} cols, {len(rows)} rows")
    cols = sorted(alive)
    return cols, [v for v in rows.values() if v], vrows


def expand(dicts, cols):
    """R-vectors -> Z-vectors (coordinate 3*col + k is the t^k coefficient)."""
    pos = {g: i for i, g in enumerate(cols)}
    out = []
    for v in dicts:
        row = [0] * (NA * len(cols))
        for g, a in v.items():
            for k in range(NA):
                row[NA * pos[g] + k] = a[k]
        out.append(row)
    return out


def shift(v, e):
    """t^e * v for an R-vector v (dict)."""
    m = mono(e)
    return {g: rmul(m, a) for g, a in v.items()}


def run(orbit, do_milp=True):
    """orbit: index into orbits.json, or 'triv' (Y = 0 check)."""
    import numpy as np
    orbs = json.load(open(os.path.join(HERE, "orbits.json")))
    flat = orbit.startswith("flat")
    idx = int(orbit[4:] if flat else orbit)
    Y, nY = orbs[idx]["Y"], orbs[idx]["n_Y"]
    extra = 0 if flat else 2
    t0 = time.time()
    T = cover_tables(Y)
    if flat:
        # check mode: forget the sheet labels.  The chains become
        # R (x) C(base) with d_1 = 0, so Q = H_1(M_3 <iota>)^3 = H_1(M_3)^3:
        # expect rank 72, torsion of M_3 three times, 135 classes, rank W 63.
        T["lab"] = [[0] * census.NGEN for _ in T["lab"]]
    log(f"cover: {len(T['qact'])} cosets over {len(T['reps'])} bases")
    gen, rels = fox_data(T)
    log(f"R-chains: {len(gen)} gens, {len(rels)} rels")
    # twist loops: one per <a1,a2,a4,a5>-orbit on the 77760 cosets
    orep, osize = threeadic.stab_orbit_reps(T["qact"])
    bs = sorted({T["base_of"][q] for q in orep})
    zs = twist_vectors(T, gen, bs)
    log(f"{len(orep)} stabilizer orbits over {len(bs)} bases")
    t1 = time.time()
    cols, R, V = eliminate_r(len(gen), rels, zs)
    t2 = time.time()
    log(f"eliminated: {len(cols)} R-cols, {len(R)} R-rels")
    Rz = expand([shift(r, e) for r in R for e in range(NA)], cols)
    zb = {b: V[i] for i, b in enumerate(bs)}
    Vz = expand([shift(zb[T["base_of"][q]], T["sheet"][q]) for q in orep],
                cols)
    nz = NA * len(cols)
    H = census.hnf_rows(Rz, nz) if Rz else []
    rankQ, tors = census.h1_invariants(H, nz) if H else (nz, [])
    b1 = rankQ - extra
    log(f"HNF done: rank Q {rankQ}, b1 {b1}, torsion {tors}")
    classes, cls_of = {}, []
    for o in range(len(orep)):
        key = census.reduce_mod_hnf(Vz[o], H)
        if key not in classes:
            classes[key] = len(classes)
        cls_of.append(classes[key])
    m = len(classes)
    rep_orb, mult = [None] * m, [0] * m
    for o in range(len(orep)):
        if rep_orb[cls_of[o]] is None:
            rep_orb[cls_of[o]] = o
        mult[cls_of[o]] += osize[o]
    B = census.w_lattice(H, [Vz[o] for o in rep_orb], nz)
    g = 0
    for r in B:
        g = int(np.gcd(g, sum(r)))
    reps = [T["orig"][orep[o]] for o in rep_orb]
    out = {"orbit": orbit, "Y": Y, "n_Y": nY, "method": "Z/3-equivariant",
           "index_in_M": len(T["qact"]), "r_gens": len(gen),
           "r_gens_after_unit_elim": len(cols), "stab_orbits": len(orep),
           "rank_Q": rankQ, "b1": b1, "torsion": tors, "classes": m,
           "class_multiplicities": sorted(mult), "rank_W": len(B),
           "gcd_aug_W": g, "W_basis": B, "class_rep_cosets": reps,
           "sec_setup": round(t1 - t0, 1), "sec_elim": round(t2 - t1, 1)}
    if do_milp and B and not flat:
        cert = census.best_certificate(B)
        out["cert_l1"], out["cert_w"] = cert
        dist = census.distance_milp(B)
        if dist is not None:
            out["distance"] = str(dist[0])
            out["optimal_h"] = dist[1]
    out["seconds"] = round(time.time() - t0, 1)
    return out


def main(argv):
    census.check_symplectic_rep()
    for a in argv:
        res = run(a)
        short = {kk: vv for kk, vv in res.items()
                 if kk not in ("W_basis", "optimal_h", "cert_w",
                               "class_rep_cosets")}
        print(json.dumps(short), flush=True)
        name = f"equivariant-orbit-{a}.json"
        with open(os.path.join(HERE, name), "w") as f:
            json.dump(res, f)


if __name__ == "__main__":
    main(sys.argv[1:])

