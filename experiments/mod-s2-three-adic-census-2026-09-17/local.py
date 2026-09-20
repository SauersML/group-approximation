#!/usr/bin/env python3
"""3-local exact Torelli census of M_Y, over the local ring (Z/3^m)[Z/3].

Same Z/3-equivariant chains as equivariant.py (Fox matrix over R = Z[Z/3]
on the 25920 base cosets of M_3<iota>), but the elimination runs over
Lam = (Z/3^m)[t]/(t^3 - 1).  Lam is local (Z/3 is a 3-group), with units
exactly the elements whose augmentation is prime to 3, so almost every
entry is a pivot candidate.  Elimination through units is an exact
isomorphism of the reduced chain complex C (x) Z/3^m, and
H_1(C (x) Z/3^m) = H_1(M_Y) (x) Z/3^m + Z/3^m-part of d_1(C_1) (H_0 is free,
no Tor term); d_1(C_1) = augmentation ideal, free of rank 2 (Y != 0).

Output (per orbit):
  * invariants of Q_m = Q (x) Z/3^m: c_m = number of summands Z/3^m
    (= b_1 + 2 + number of 3-torsion summands of order >= 3^m), and the
    smaller 3-power torsion;
  * L_m = {w in Z^classes : sum w_c v_c in 3^m H_1(M_Y)} (a lattice
    containing 3^m Z^classes and W(G_Y));
  * for n_Y = 0 (classes = the 45 level-3 splittings, Lemma A.3):
    W(G_Y) = W(Gamma(3)) cap L_m, valid when the 3-torsion of H_1(M_Y) has
    exponent < 3^m, which holds when c_m = 26 (b_1 = 24 is Lemma A.3);
    then d(G_Y), gcd aug and an l1-optimal certificate.
Usage: python3 local.py <m> <orbit> ...      ('flat<a>': sheet labels 0,
expect c_m = 72.)
"""
import json
import os
import sys
import time

import numpy as np

import equivariant as eq
from equivariant import census, log, threeadic
from compare import split_key, G3, lattice_index

HERE = os.path.dirname(os.path.abspath(__file__))
NA = 3
MOD = None          # 3^m, set in main


def lmul(x, y):
    return tuple(sum(x[i] * y[(k - i) % NA] for i in range(NA)) % MOD
                 for k in range(NA))


def lsub_mul(a, f, b):
    fb = lmul(f, b)
    return tuple((a[k] - fb[k]) % MOD for k in range(NA))


_INV = {}


def linv(u):
    """Inverse in Lam, or None if u is not a unit."""
    if u in _INV:
        return _INV[u]
    s = sum(u) % 3
    if s == 0:
        _INV[u] = None
        return None
    c = pow(sum(u) % MOD, -1, MOD)
    x = (c, 0, 0)
    for _ in range(8):            # Newton: error e -> e^2, m^(3m) = 0
        ux = lmul(u, x)
        x = lmul(x, ((2 - ux[0]) % MOD, (-ux[1]) % MOD, (-ux[2]) % MOD))
    assert lmul(u, x) == (1, 0, 0)
    _INV[u] = x
    return x


def reduce_vec(v):
    return {g: tuple(a % MOD for a in x) for g, x in v.items()
            if any(a % MOD for a in x)}


def eliminate_local(ngen, rels, vs):
    """Unit elimination over Lam (Markowitz within the row)."""
    rows = {r: reduce_vec(v) for r, v in enumerate(rels)}
    rows = {r: v for r, v in rows.items() if v}
    colrows = {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    vrows = [reduce_vec(v) for v in vs]
    vcol = {}
    for t, v in enumerate(vrows):
        for g in v:
            vcol.setdefault(g, set()).add(t)
    alive = set(range(ngen))

    def reduce(row, rid, cmap, j, pinv, piv):
        f = lmul(row[j], pinv)
        for g, b in piv.items():
            nv = lsub_mul(row.get(g, (0,) * NA), f, b)
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
        done = 0
        for r in sorted(rows, key=lambda r: len(rows[r])):
            if r not in rows:
                continue
            v = rows[r]
            if not v:
                del rows[r]
                continue
            units = [g for g, a in v.items() if linv(a) is not None]
            if not units:
                continue
            j = min(units, key=lambda g: len(colrows.get(g, ())))
            pinv = linv(v[j])
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
            done += 1
            if done % 20000 == 0:
                log(f"  pass {npass}: {done} pivots, {len(rows)} rows left")
        log(f"pass {npass}: {len(alive)} cols, {len(rows)} rows")
    cols = sorted(alive)
    return cols, [v for v in rows.values() if v], vrows


def shift(v, e):
    m = eq.mono(e)
    return {g: lmul(m, a) for g, a in v.items()}


def eliminate_c(ngen, rels, vs):
    """Same elimination in C (lelim.c, compiled to $LELIM_BIN); files in
    $LELIM_TMP."""
    import subprocess
    tmp = os.environ["LELIM_TMP"]
    fin = os.path.join(tmp, f"lelim-in-{os.getpid()}.txt")
    fout = os.path.join(tmp, f"lelim-out-{os.getpid()}.txt")
    with open(fin, "w") as f:
        f.write(f"{ngen} {len(rels)} {len(vs)} {MOD}\n")
        for v in list(rels) + list(vs):
            parts = [str(len(v))]
            for g, a in v.items():
                parts.append(f"{g} {a[0]} {a[1]} {a[2]}")
            f.write(" ".join(parts) + "\n")
    log("lelim input written")
    with open(fin) as fi, open(fout, "w") as fo:
        subprocess.run([os.environ["LELIM_BIN"]], stdin=fi, stdout=fo,
                       check=True)
    os.remove(fin)
    with open(fout) as f:
        tok = f.read().split("\n")
    os.remove(fout)
    pos = 0
    na = int(tok[pos]); pos += 1
    cols = [int(tok[pos + i]) for i in range(na)]; pos += na

    def parse(line):
        x = [int(s) for s in line.split()]
        return {x[1 + 4 * k]: tuple(x[2 + 4 * k: 5 + 4 * k])
                for k in range(x[0])}
    nr = int(tok[pos]); pos += 1
    R = [parse(tok[pos + i]) for i in range(nr)]; pos += nr
    nv = int(tok[pos]); pos += 1
    V = [parse(tok[pos + i]) for i in range(nv)]
    return cols, R, V


def intersect_rowspaces(A, B):
    """Basis of rowspace_Z(A) cap rowspace_Z(B) (A, B lists of rows)."""
    n, ra = len(A[0]), len(A)
    big = [list(a) + [1 if i == k else 0 for i in range(ra)]
           for k, a in enumerate(A)]
    big += [list(b) + [0] * ra for b in B]
    H = census.hnf_rows(big, n + ra)
    ys = [r[n:] for r in H if not any(r[:n])]
    out = [[sum(y[k] * A[k][j] for k in range(ra)) for j in range(n)]
           for y in ys]
    return census.hnf_rows(out, n)


def in_rowspace(x, H):
    return not any(census.reduce_mod_hnf(x, H))


def run(orbit, do_milp=True):
    orbs = json.load(open(os.path.join(HERE, "orbits.json")))
    flat = orbit.startswith("flat")
    idx = int(orbit[4:] if flat else orbit)
    Y, nY = orbs[idx]["Y"], orbs[idx]["n_Y"]
    t0 = time.time()
    T = eq.cover_tables(Y)
    if flat:
        T["lab"] = [[0] * census.NGEN for _ in T["lab"]]
    gen, rels = eq.fox_data(T)
    log(f"R-chains: {len(gen)} gens, {len(rels)} rels; modulus {MOD}")
    orep, osize = threeadic.stab_orbit_reps(T["qact"])
    bs = sorted({T["base_of"][q] for q in orep})
    zs = eq.twist_vectors(T, gen, bs)
    del T["D"], T["tree"]
    t1 = time.time()
    if os.environ.get("LELIM_BIN"):
        cols, R, V = eliminate_c(len(gen), rels, zs)
    else:
        cols, R, V = eliminate_local(len(gen), rels, zs)
    del rels
    t2 = time.time()
    nz = NA * len(cols)
    Rz = eq.expand([shift(r, e) for r in R for e in range(NA)], cols)
    Rz += [[MOD if i == k else 0 for i in range(nz)] for k in range(nz)]
    zb = {b: V[i] for i, b in enumerate(bs)}
    Vz = eq.expand([shift(zb[T["base_of"][q]], T["sheet"][q]) for q in orep],
                   cols)
    H = census.hnf_rows(Rz, nz)
    _, inv = census.h1_invariants(H, nz)
    c_m = sum(1 for d in inv if d == MOD)
    small = sorted(d for d in inv if d != MOD)
    log(f"eliminated to {len(cols)} R-cols; c_m = {c_m}, smaller {small}")
    out = {"orbit": orbit, "Y": Y, "n_Y": nY, "modulus": MOD,
           "method": "Z/3-equivariant over (Z/3^m)[Z/3]",
           "r_gens": len(gen), "r_gens_after_unit_elim": len(cols),
           "stab_orbits": len(orep), "c_m": c_m, "smaller_invariants": small,
           "b1_upper_bound": c_m - (0 if flat else 2),
           "sec_setup": round(t1 - t0, 1), "sec_elim": round(t2 - t1, 1)}
    if flat:
        out["seconds"] = round(time.time() - t0, 1)
        return out
    # group twist loops into conjugacy classes
    lift = T["lift"]
    skey = [split_key(lift[T["orig"][q] // 3]) for q in orep]
    red = [census.reduce_mod_hnf(v, H) for v in Vz]
    if nY == 0:
        gkey = skey
    else:
        gkey = [(skey[o], red[o]) for o in range(len(orep))]
    groups = {}
    for o, k in enumerate(gkey):
        groups.setdefault(k, []).append(o)
    consistent = all(len({red[o] for o in os_}) == 1
                     for os_ in groups.values())
    out["classes"] = len(groups)
    out["expected_classes"] = 45 + 2 * nY
    out["group_vectors_consistent"] = consistent
    out["splittings_hit"] = len(set(skey))
    g3 = json.load(open(G3))[0]
    keys3 = [split_key(o) for o in g3["class_rep_objects"]]
    pos3 = {k: i for i, k in enumerate(keys3)}
    W3 = g3["W_basis"]
    if nY == 0:
        assert consistent and len(groups) == 45
        order = sorted(groups, key=lambda k: pos3[k])
        assert [pos3[k] for k in order] == list(range(45))
        Vc = [Vz[groups[k][0]] for k in order]
        L = census.hnf_rows(census.w_lattice(H, Vc, nz), 45)
        out["transfer_check_3W3_in_L"] = all(
            in_rowspace([3 * a for a in b], L) for b in W3)
        out["W3_in_L"] = all(in_rowspace(b, L) for b in W3)
        WY = intersect_rowspaces(W3, L)
        G = census.hnf_rows(WY, 45)
        out["rank_W"] = len(G)
        out["W_basis"] = G
        elem, _, _ = lattice_index(G, W3)
        out["index_in_W3_elementary_divisors"] = elem
        g = 0
        for r in G:
            g = int(np.gcd(g, sum(r)))
        out["gcd_aug_W"] = g
        out["exact"] = (c_m == 26)
        if do_milp and G:
            cert = census.best_certificate(G)
            out["cert_l1"], out["cert_w"] = cert
            dist = census.distance_milp(G)
            if dist is not None:
                out["distance"] = str(dist[0])
                out["optimal_h"] = dist[1]
    else:
        # 3-local data only: classes over each splitting, and L_m
        per_s = {}
        for k in groups:
            per_s[k[0]] = per_s.get(k[0], 0) + 1
        out["classes_per_splitting"] = sorted(per_s.values())
        order = sorted(groups, key=lambda k: (pos3[k[0]], k[1]))
        c3 = [pos3[k[0]] for k in order]
        out["class_splitting_pos3"] = c3
        ncl = len(order)
        Vc = [Vz[groups[k][0]] for k in order]
        L = census.hnf_rows(census.w_lattice(H, Vc, nz), ncl)
        first = {}
        for i, c in enumerate(c3):
            first.setdefault(c, i)
        # transfer of W3 (sum over the classes above c, 3 e_c if unsplit)
        tr = []
        for b in W3:
            w = [0] * ncl
            for i, c in enumerate(c3):
                w[i] += b[c] * (3 if per_s[order[i][0]] == 1 else 1)
            tr.append(w)
        out["transfer_W3_in_L"] = all(in_rowspace(w, L) for w in tr)
        # P = push^-1(W3): lifts of W3 plus the kernel of push
        P = []
        for b in W3:
            w = [0] * ncl
            for c, i in first.items():
                w[i] = b[c]
            P.append(w)
        for i, c in enumerate(c3):
            if first[c] != i:
                w = [0] * ncl
                w[i], w[first[c]] = 1, -1
                P.append(w)
        WY = intersect_rowspaces(P, L)
        G = census.hnf_rows(WY, ncl)
        out["rank_W"] = len(G)
        out["W_basis"] = G
        g = 0
        for r in G:
            g = int(np.gcd(g, sum(r)))
        out["gcd_aug_W"] = g
        out["exact_3local"] = (c_m == 26)
        if do_milp and G:
            cert = census.best_certificate(G)
            out["cert_l1"], out["cert_w"] = cert
            dist = census.distance_milp(G)
            if dist is not None:
                out["distance"] = str(dist[0])
                out["optimal_h"] = dist[1]
    out["seconds"] = round(time.time() - t0, 1)
    return out


def main(argv):
    global MOD
    MOD = 3 ** int(argv[0])
    census.check_symplectic_rep()
    for a in argv[1:]:
        res = run(a)
        short = {kk: vv for kk, vv in res.items()
                 if kk not in ("W_basis", "optimal_h", "cert_w",
                               "class_splitting_pos3")}
        print(json.dumps(short), flush=True)
        with open(os.path.join(HERE, f"local-orbit-{a}.json"), "w") as f:
            json.dump(res, f)


if __name__ == "__main__":
    main(sys.argv[1:])
