#!/usr/bin/env python3
"""Torelli-scalar census for the index-3 subgroups Gamma(9) < G_Y < Gamma(3).

G_Y = {g in Gamma(3) : tr(Y X) = 0 mod 3 where g = I + 3X mod 9}, Y from
orbits.json.  Cosets of M_Y = pi^{-1}(G_Y) in M = Mod(S_2) are pairs
(gbar, c), gbar in Sp_4(F_3), c in F_3, with right action
    (gbar, c) . a_i = (gbar A_i, c + chi_Y(s(gbar) A_i s(gbar A_i)^{-1})),
s a fixed mod-9 section (BFS tree products).  The pipeline after the coset
table is census.py's (abelianised Reidemeister-Schreier, exact elimination,
W lattice, d by MILP, l1-optimal certificate).

Usage: python3 threeadic.py <orbit index into orbits.json> ...
"""
import importlib.util
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "census", os.path.join(HERE, "..", "mod-s2-torelli-scalar-census-2026-09-17",
                           "census.py"))
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)

J = census.J
GEN9 = [A % 9 for A in census.GENMATS]


def inv9(A):
    return (-J @ A.T @ J) % 9


def key3(A):
    return tuple(int(t) for t in (A % 3).flatten())


def section():
    """BFS over Sp_4(F_3) by right multiplication; s(gbar) mod 9."""
    I = np.eye(4, dtype=np.int64)
    idx = {key3(I): 0}
    lift = [I]
    q = 0
    while q < len(lift):
        g = lift[q]
        for A in GEN9:
            h = (g @ A) % 9
            k = key3(h)
            if k not in idx:
                idx[k] = len(lift)
                lift.append(h)
        q += 1
    assert len(lift) == 51840
    return idx, lift


def coset_table(Y):
    idx, lift = section()
    Y = np.array(Y, dtype=np.int64) % 3
    n = len(lift)
    act = []
    for c in range(3 * n):
        gi, cc = divmod(c, 3)
        g = lift[gi]
        row = []
        for A in GEN9:
            h = (g @ A) % 9
            gj = idx[key3(h)]
            u = (h @ inv9(lift[gj])) % 9          # = I + 3X mod 9
            assert ((u - np.eye(4, dtype=np.int64)) % 3 == 0).all()
            X = ((u - np.eye(4, dtype=np.int64)) // 3) % 3
            phi = int(np.trace(Y @ X)) % 3
            row.append(3 * gj + (cc + phi) % 3)
        act.append(row)
    return act, lift


def relators_mod_iota():
    """Presentation of M/<iota> = Mod(S_{0,6}): add iota = 1 to census.py's
    presentation of M; iota^2 = 1 and centrality become redundant."""
    NG = census.NGEN
    rels = []
    for i in range(NG - 1):
        rels.append(([i, i + 1, i], [i + 1, i, i + 1]))
    for i in range(NG):
        for j in range(i + 2, NG):
            rels.append(([i, j], [j, i]))
    rels.append(([0, 1, 2, 3, 4] * 6, []))
    rels.append((list(census.IOTA), []))
    return rels


def quotient_table(act):
    """Cosets of M_Y <iota> from cosets of M_Y.  iota is central and
    -I is not I mod 3, so iota is not in M_Y and M_Y -> M/<iota> is injective
    with image of index len(act)/2.  Objects are the pairs {o, o.iota}."""
    k = len(act)
    iota = [census.trace_perm(act, c, census.IOTA) for c in range(k)]
    assert all(iota[iota[c]] == c and iota[c] != c for c in range(k))
    rep = [min(c, iota[c]) for c in range(k)]
    order = sorted(set(rep))
    # BFS renumbering so that the base pair {0, iota(0)} gets index 0
    new = {rep[0]: 0}
    queue = [rep[0]]
    for r in queue:
        for i in range(census.NGEN):
            s = rep[act[r][i]]
            if s not in new:
                new[s] = len(queue)
                queue.append(s)
    assert len(queue) == len(order) == k // 2
    qact = [[new[rep[act[r][i]]] for i in range(census.NGEN)] for r in queue]
    return qact, queue


def splitting_key(g):
    """Key of the level-3 splitting g(P), P = span(e0, e1) (columns)."""
    u, v = g[:, 0] % 3, g[:, 1] % 3
    span = frozenset(tuple(int(t) for t in (a * u + b * v) % 3)
                     for a in range(3) for b in range(3) if a or b)
    return span


def log(msg):
    import resource
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
    print(f"[{time.strftime('%H:%M:%S')}] {msg} (peak rss {rss:.2f} GB)",
          file=sys.stderr, flush=True)


def stab_orbit_reps(act):
    """Orbits of <a1, a2, a4, a5> (letters 0, 1, 3, 4) on cosets: minimal
    representative and size of each."""
    k = len(act)
    orb_of = [-1] * k
    orep, osize = [], []
    for c0 in range(k):
        if orb_of[c0] >= 0:
            continue
        o = len(orep)
        orep.append(c0)
        orb_of[c0] = o
        stack, n = [c0], 0
        while stack:
            c = stack.pop()
            n += 1
            for i in (0, 1, 3, 4):
                d = act[c][i]
                if orb_of[d] < 0:
                    orb_of[d] = o
                    stack.append(d)
        osize.append(n)
    return orep, osize


def run(orbit_index, do_milp=True):
    orbs = json.load(open(os.path.join(HERE, "orbits.json")))
    Y = orbs[orbit_index]["Y"]
    t0 = time.time()
    act, lift = coset_table(Y)
    log(f"coset table {len(act)}")
    census.check_action(act)
    act, orig = quotient_table(act)
    census.relators = relators_mod_iota      # used by check_action, rs_data
    census.check_action(act)
    log(f"quotient by iota: {len(act)} cosets")
    k = len(act)
    ngen, rels, vs = census.rs_data(act)
    t1 = time.time()
    log(f"rs data: {ngen} gens, {len(rels)} rels")
    # T_S = (a1 a2)^6 commutes with a1, a2, a4, a5 in M, so the twist loops at
    # c and c.a_i (i in 0,1,3,4) are homologous: keep one loop per orbit of
    # <a1,a2,a4,a5> on cosets (this is what keeps the elimination small).
    orep, osize = stab_orbit_reps(act)
    vs = [vs[c] for c in orep]
    log(f"{len(orep)} stabilizer orbits of twist loops")
    cols, R, V = census.unit_eliminate(ngen, rels, vs)
    t2 = time.time()
    log(f"eliminated: {len(cols)} cols, {len(R)} rels")
    Rd = census.to_dense(R, cols)
    Vd = census.to_dense(V, cols)
    H = census.hnf_rows(Rd, len(cols)) if Rd else []
    b1, tors = census.h1_invariants(H, len(cols)) if H else (len(cols), [])
    classes, cls_of = {}, []
    for o in range(len(orep)):
        key = census.reduce_mod_hnf(Vd[o], H)
        if key not in classes:
            classes[key] = len(classes)
        cls_of.append(classes[key])
    m = len(classes)
    reps = [None] * m
    rep_orb = [None] * m
    mult = [0] * m
    for o in range(len(orep)):
        if reps[cls_of[o]] is None:
            reps[cls_of[o]] = orep[o]
            rep_orb[cls_of[o]] = o
        mult[cls_of[o]] += osize[o]
    Vr = [Vd[o] for o in rep_orb]
    B = census.w_lattice(H, Vr, len(cols))
    augs = [sum(r) for r in B]
    g = 0
    for a in augs:
        g = int(np.gcd(g, a))
    # level-3 splitting under each class (P and P^perp give the same twist
    # class; record the plane spanned by the first two columns)
    reps = [orig[c] for c in reps]            # cosets of M_Y (pair minima)
    spl = [sorted(sorted(p) for p in [splitting_key(lift[reps[j] // 3])])
           for j in range(m)]
    out = {"orbit": orbit_index, "Y": Y, "n_Y": orbs[orbit_index]["n_Y"],
           "index_in_M": k, "schreier_gens": ngen,
           "gens_after_unit_elim": len(cols), "stab_orbits": len(orep),
           "b1": b1, "torsion": tors,
           "classes": m, "class_multiplicities": sorted(mult),
           "rank_W": len(B), "gcd_aug_W": g, "W_basis": B,
           "class_rep_cosets": reps, "class_plane": spl,
           "sec_rs": round(t1 - t0, 1), "sec_elim": round(t2 - t1, 1)}
    if do_milp and B:
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
        res = run(int(a))
        short = {kk: vv for kk, vv in res.items()
                 if kk not in ("W_basis", "optimal_h", "cert_w",
                               "class_rep_cosets", "class_plane")}
        print(json.dumps(short), flush=True)
        with open(os.path.join(HERE, f"threeadic-orbit-{a}.json"), "w") as f:
            json.dump(res, f)


if __name__ == "__main__":
    main(sys.argv[1:])
