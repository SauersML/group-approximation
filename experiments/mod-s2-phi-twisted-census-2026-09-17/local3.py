#!/usr/bin/env python3
"""3-local exact Torelli census of M_L, L an order-3 subgroup of Phi, from
the R-chains of twisted.py, over Lam = (Z/3^m)[t]/(t^3 - 1).

Lam is local, with units the elements whose augmentation is prime to 3.
Unit elimination (lelim.c, compiled to $LELIM_BIN) is an exact isomorphism
of Q (x) Z/3^m, Q = C_1/rows = H_1(M_L) + I_R (I_R = Z^2 free, so
Q (x) Z/3^m = H_1(M_L) (x) Z/3^m + (Z/3^m)^2).  Output:

  * c_m = number of Z/3^m summands of Q (x) Z/3^m
        = b_1(M_L) + 2 + #(3-torsion summands of order >= 3^m);
  * the classes of the twist loops t^s z_{c,A}, grouped by
    (class in H_1(M_Phi) [phi-base.json], image in Q (x) Z/3^m);
  * L_m = {w : sum w_i v_i in 3^m Q}, P = push^-1 W(Phi) (lifts of a basis
    of W(Phi) plus fibre differences), and P cap L_m.

Exactness (proof node): if H_1(M_Phi; Z[omega,1/3]_chi) = 0 (zomega.py:
Q_omega (x) Z[1/3] = Z[1/3, omega]) then b_1(M_L) = 30 and
K = ker(H_1(M_L) -> H_1(M_Phi)) is a finite 3-group; if moreover
c_m = 32, the 3-torsion of H_1(M_L) has exponent < 3^m, the grouping is the
exact class partition, and W(Gamma_L) = P cap L_m.

Usage: LELIM_BIN=... LELIM_TMP=... python3 local3.py <m> <L index | z>
       [phi-base.json] [out.json]
"""
import json
import os
import subprocess
import sys
import time
from math import gcd

import numpy as np

import twisted as T
import sylow as S

C = S.C
HERE = os.path.dirname(os.path.abspath(__file__))
MOD = None


def shift(v, e):
    return {g: [a[(k - e) % 3] for k in range(3)] for g, a in v.items()}


def lelim(ngen, rels, vs):
    tmp = os.environ["LELIM_TMP"]
    fin = os.path.join(tmp, f"l3-in-{os.getpid()}.txt")
    fout = os.path.join(tmp, f"l3-out-{os.getpid()}.txt")
    with open(fin, "w") as f:
        f.write(f"{ngen} {len(rels)} {len(vs)} {MOD}\n")
        for v in list(rels) + list(vs):
            parts = [str(len(v))]
            for g, a in v.items():
                parts.append(f"{g} {a[0]} {a[1]} {a[2]}")
            f.write(" ".join(parts) + "\n")
    with open(fin) as fi, open(fout, "w") as fo:
        subprocess.run([os.environ["LELIM_BIN"]], stdin=fi, stdout=fo,
                       check=True)
    os.remove(fin)
    tok = open(fout).read().split("\n")
    os.remove(fout)
    pos = 0
    na = int(tok[pos]); pos += 1
    cols = [int(tok[pos + i]) for i in range(na)]; pos += na

    def parse(line):
        x = [int(s) for s in line.split()]
        return {x[1 + 4 * k]: list(x[2 + 4 * k: 5 + 4 * k])
                for k in range(x[0])}
    nr = int(tok[pos]); pos += 1
    R = [parse(tok[pos + i]) for i in range(nr)]; pos += nr
    nv = int(tok[pos]); pos += 1
    V = [parse(tok[pos + i]) for i in range(nv)]
    return cols, R, V


def expand(vs, cols):
    ci = {g: 3 * i for i, g in enumerate(cols)}
    n = 3 * len(cols)
    out = np.zeros((len(vs), n), dtype=np.int64)
    for r, v in enumerate(vs):
        for g, a in v.items():
            for k in range(3):
                out[r, ci[g] + k] = a[k]
    return out % MOD


def reduce_all(X, H):
    """Reduce every row of X modulo the HNF H (a lattice containing
    MOD Z^n), keeping entries in [0, MOD)."""
    X = X.copy() % MOD
    for r in H:
        p = next(j for j, a in enumerate(r) if a)
        h = np.array(r, dtype=np.int64)
        q = X[:, p] // r[p]
        X = (X - np.outer(q, h)) % MOD
    return X


def intersect_rowspaces(A, B):
    n, ra = len(A[0]), len(A)
    big = [list(a) + [1 if i == k else 0 for i in range(ra)]
           for k, a in enumerate(A)]
    big += [list(b) + [0] * ra for b in B]
    H = C.hnf_rows(big, n + ra)
    ys = [r[n:] for r in H if not any(r[:n])]
    out = [[sum(y[k] * A[k][j] for k in range(ra)) for j in range(n)]
           for y in ys]
    return C.hnf_rows(out, n)


def in_rowspace(x, H):
    return not any(C.reduce_mod_hnf(x, H))


def main(m, which, basep, outp):
    global MOD
    MOD = 3 ** m
    t0 = time.time()
    ngen, R, Z, zinfo, info = T.build(which)
    cols, Rr, V = lelim(ngen, R, Z)
    del R, Z
    T.log(f"lelim: {len(cols)} R-cols, {len(Rr)} rows left "
          f"[{time.time()-t0:.0f}s]")
    nz = 3 * len(cols)
    Rz = expand([shift(r, e) for r in Rr for e in range(3)], cols)
    Rz = {tuple(int(a) for a in row) for row in Rz if row.any()}
    Rz = [list(r) for r in sorted(Rz)]
    Rz += [[MOD if i == k else 0 for i in range(nz)] for k in range(nz)]
    H = []
    for k in range(0, len(Rz), 2000):
        H = C.hnf_rows(H + Rz[k:k + 2000], nz)
    _, inv = C.h1_invariants(H, nz)
    c_m = sum(1 for d in inv if d == MOD)
    small = sorted(d for d in inv if d != MOD)
    T.log(f"c_m = {c_m}, smaller invariants {small} [{time.time()-t0:.0f}s]")
    while not os.path.exists(basep):      # phi_base.py may still run
        time.sleep(30)
    time.sleep(5)
    base = json.load(open(basep))
    cls_phi, W_phi = base["cls_of"], base["W_basis"]
    nphi = base["classes"]
    assert len(zinfo) == len(cls_phi)
    # twist loops t^s z_i, i = (c, A)
    keys, members = {}, []
    cl = [[None] * len(V) for _ in range(3)]
    for s in range(3):
        X = reduce_all(expand([shift(v, s) for v in V], cols), H)
        for i in range(len(V)):
            k = (cls_phi[i], X[i].tobytes())
            if k not in keys:
                keys[k] = len(keys)
                members.append((i, s, X[i].copy()))
            cl[s][i] = keys[k]
    ncl = len(keys)
    phi_of = [k[0] for k in sorted(keys, key=lambda k: keys[k])]
    per = {}
    for c in phi_of:
        per[c] = per.get(c, 0) + 1
    T.log(f"{ncl} classes over {len(per)} Phi-classes, fibre sizes "
          f"{sorted(set(per.values()))}")
    assert len(per) == nphi
    Vc = [[int(a) for a in x] for _, _, x in members]
    L = C.hnf_rows(C.w_lattice(H, Vc, nz), ncl)
    first = {}
    for i, c in enumerate(phi_of):
        first.setdefault(c, i)
    P = []
    for b in W_phi:
        w = [0] * ncl
        for c, i in first.items():
            w[i] = b[c]
        P.append(w)
    for i, c in enumerate(phi_of):
        if first[c] != i:
            w = [0] * ncl
            w[i], w[first[c]] = 1, -1
            P.append(w)
    # transfer of W(Phi): [z_i] -> sum_s [t^s z_i]
    rep = {}
    for i, c in enumerate(cls_phi):
        rep.setdefault(c, i)
    tr = []
    for b in W_phi:
        w = [0] * ncl
        for c, i in rep.items():
            for s in range(3):
                w[cl[s][i]] += b[c]
        tr.append(w)
    G = C.hnf_rows(intersect_rowspaces(P, L), ncl)
    g = 0
    for r in G:
        g = gcd(g, sum(r))
    out = dict(info)
    out.update({"modulus": MOD, "r_cols_after_unit_elim": len(cols),
                "c_m": c_m, "smaller_invariants": small,
                "classes": ncl, "phi_classes": nphi,
                "fibre_sizes": {str(k): v for k, v in
                                sorted(((s, sum(1 for x in per.values()
                                             if x == s))
                                        for s in set(per.values())))},
                "transfer_W_phi_in_L": all(in_rowspace(w, L) for w in tr),
                "transfer_W_phi_in_PcapL": all(in_rowspace(w, G) for w in tr),
                "rank_P": len(C.hnf_rows(P, ncl)), "rank_L": len(L),
                "rank_W": len(G), "gcd_aug_W": g,
                "exact_if_twisted_vanishing": c_m == 32})
    T.log(json.dumps(out))
    if G:
        dist = C.distance_milp(G)
        if dist is not None:
            out["d"] = str(dist[0])
            out["theta_values"] = sorted(set(dist[1]))
        l1, w = C.best_certificate(G)
        out["cert_l1"], out["cert_aug"] = l1, (sum(w) if w else None)
        ap, wp = S.positive_certificate(G)
        out["A_plus"] = ap
        out["A_plus_support"] = sum(1 for a in wp if a) if wp else None
    out["seconds"] = round(time.time() - t0)
    print(json.dumps(out), flush=True)
    out["W_basis"] = G
    out["phi_class_of_class"] = phi_of
    if outp:
        json.dump(out, open(outp, "w"))


if __name__ == "__main__":
    a = sys.argv[1:]
    main(int(a[0]), a[1],
         a[2] if len(a) > 2 else os.path.join(HERE, "phi-base.json"),
         a[3] if len(a) > 3 else None)
