#!/usr/bin/env python3
"""v5: joint floor over exact block-unitary K in Z = rho(G)' AND the
residual torsor W in U(rho(Q1)'), at the control dictionary V0.

min over (K, W) of |<V0 W K W* V0*, K>| / D  with |tau K| <= 0.05.
If positive across a dense multistart, the prototype floor holds
against all low-defect dictionaries (V ~ V0 W cosets).
"""
import json
import sys

import numpy as np

exec(open("sl3_delta3_probe_v3.py").read().split("def main()")[0])

GENS_Q1 = [m2 for m2 in [
    [[1, 1, 0], [0, 1, 0], [0, 0, 1]],
    [[1, 0, 1], [0, 1, 0], [0, 0, 1]],
    [[1, 0, 0], [0, 1, 1], [0, 0, 1]],
    [[1, 0, 0], [2, 1, 0], [0, 0, 1]],
    [[1, 0, 0], [0, 1, 0], [4, 0, 1]],
    [[1, 0, 0], [0, 1, 0], [0, 2, 1]]]]


def orbit_labels(gens):
    perms = [perm_of(g) for g in gens]
    n = D * D
    parent = np.arange(n, dtype=np.int64)

    def find(a):
        r = a
        while parent[r] != r:
            r = parent[r]
        while parent[a] != r:
            parent[a], a = r, parent[a]
        return r

    changed = True
    while changed:
        changed = False
        for p in perms:
            for x in range(D):
                px = p[x] * D
                xD = x * D
                for y in range(D):
                    a = find(xD + y)
                    b = find(px + p[y])
                    if a != b:
                        parent[a] = b
                        changed = True
    roots = {}
    lab = np.empty(n, dtype=np.int64)
    for i in range(n):
        r = find(i)
        if r not in roots:
            roots[r] = len(roots)
        lab[i] = roots[r]
    return len(roots), lab.reshape(D, D)


def block_iso(gens, seed):
    """Isometry lists per irrep-block of the commutant of the perm rep
    of <gens>, via generic-element eigenprojections + connectivity."""
    nor, LAB = orbit_labels(gens)
    mats = [(LAB == i).astype(np.float64) for i in range(nor)]
    rngA = np.random.default_rng(seed)
    A = np.zeros((D, D))
    for i in range(nor):
        A += rngA.normal() * mats[i]
    A = (A + A.T) / 2.0
    ev, U = np.linalg.eigh(A)
    clusters = []
    start = 0
    for i in range(1, D + 1):
        if i == D or abs(ev[i] - ev[i - 1]) > 1e-7:
            clusters.append((start, i))
            start = i
    B2 = np.zeros((D, D))
    for i in range(nor):
        B2 += rngA.normal() * mats[i]
    B2 = (B2 + B2.T) / 2.0
    ncl = len(clusters)
    comp = [-1] * ncl
    nc = 0
    for i in range(ncl):
        if comp[i] >= 0:
            continue
        stack = [i]
        while stack:
            x = stack.pop()
            if comp[x] >= 0:
                continue
            comp[x] = nc
            s0, s1 = clusters[x]
            for y in range(ncl):
                if comp[y] >= 0:
                    continue
                t0, t1 = clusters[y]
                if (s1 - s0) != (t1 - t0):
                    continue
                blk = U[:, s0:s1].T @ B2 @ U[:, t0:t1]
                if np.linalg.norm(blk) > 1e-6:
                    stack.append(y)
        nc += 1
    blocks = {}
    for i, c_ in enumerate(comp):
        blocks.setdefault(c_, []).append(i)
    binfo = []
    for c_, cl in blocks.items():
        binfo.append([U[:, clusters[k][0]:clusters[k][1]] for k in cl])
    prof = sorted((len(v), clusters[v[0]][1] - clusters[v[0]][0])
                  for v in blocks.values())
    return binfo, prof, nor


def unitary_from(binfo, params):
    K = np.zeros((D, D), dtype=complex)
    for iso, X in zip(binfo, params):
        m_ = len(iso)
        for a_ in range(m_):
            for b_ in range(m_):
                if abs(X[a_, b_]) > 1e-12:
                    K += X[a_, b_] * (iso[a_] @ iso[b_].conj().T)
    return K


def rand_params(binfo, rngu):
    ps = []
    for iso in binfo:
        m_ = len(iso)
        Zm = rngu.normal(size=(m_, m_)) + 1j * rngu.normal(size=(m_, m_))
        ps.append(np.linalg.qr(Zm)[0])
    return ps


def main():
    pl = [(perm_of(a), perm_of(b)) for a, b in PLIST]
    pli = [(inv_perm(a), inv_perm(b)) for a, b in pl]

    def defect_V(V):
        f = 0.0
        for (pa, pb), (pai, pbi) in zip(pl, pli):
            W = V[:, pa] @ V.conj().T
            f += 2 - 2 * np.real(np.trace(W[pbi, :]) / D)
        return f

    rng2 = np.random.default_rng(777)
    V = np.linalg.qr(rng2.normal(size=(D, D)) +
                     1j * rng2.normal(size=(D, D)))[0]
    step = 0.5
    for it in range(260):
        f0 = defect_V(V)
        NV = np.zeros((D, D), dtype=complex)
        for (pa, pb), (pai, pbi) in zip(pl, pli):
            Wm = V[:, pa] @ V.conj().T
            NV += -(2.0 / D) * (Wm[:, pbi] - Wm[pb, :])
        Y = (NV - NV.conj().T) / 2.0
        nn = max(np.linalg.norm(Y), 1e-14)
        A = (step / nn) * Y
        V2 = np.linalg.solve(np.eye(D) - A / 2, (np.eye(D) + A / 2) @ V)
        if defect_V(V2) < f0:
            V = V2
            step = min(step * 1.2, 1.0)
        else:
            step *= 0.5
            if step < 1e-7:
                break
    D0 = defect_V(V)

    bZ, profZ, norZ = block_iso(GENS_G, 4242)
    bQ, profQ, norQ = block_iso(GENS_Q1, 555)
    print(json.dumps({"D0": round(float(D0), 5), "dimZ": norZ,
                      "dimQ1c": norQ, "profZ": profZ,
                      "profQ1": profQ[:10]}), flush=True)

    rngu = np.random.default_rng(303)
    best = None
    for restart in range(40):
        pk = rand_params(bZ, rngu)
        pw = rand_params(bQ, rngu)
        K = unitary_from(bZ, pk)
        Wt = unitary_from(bQ, pw)
        KW = Wt @ K @ Wt.conj().T
        lk = abs(np.vdot(K, V @ KW @ V.conj().T)) / D
        tk = abs(np.trace(K)) / D
        cur = lk + 10.0 * max(0.0, tk - 0.05)
        T = 0.3
        for it in range(500):
            which = rngu.integers(0, 2)
            if which == 0:
                j = rngu.integers(0, len(pk))
                m_ = pk[j].shape[0]
            else:
                j = rngu.integers(0, len(pw))
                m_ = pw[j].shape[0]
            Zm = rngu.normal(size=(m_, m_)) + 1j * rngu.normal(size=(m_, m_))
            Xm = (Zm - Zm.conj().T) / 2
            if which == 0:
                pk2 = [p.copy() for p in pk]
                pk2[j] = np.linalg.solve(np.eye(m_) - T / 2 * Xm,
                                         (np.eye(m_) + T / 2 * Xm) @ pk[j])
                K2 = unitary_from(bZ, pk2)
                KW2 = Wt @ K2 @ Wt.conj().T
                lk2 = abs(np.vdot(K2, V @ KW2 @ V.conj().T)) / D
                tk2 = abs(np.trace(K2)) / D
                c2 = lk2 + 10.0 * max(0.0, tk2 - 0.05)
                if c2 < cur:
                    pk, K, cur = pk2, K2, c2
                else:
                    T *= 0.997
            else:
                pw2 = [p.copy() for p in pw]
                pw2[j] = np.linalg.solve(np.eye(m_) - T / 2 * Xm,
                                         (np.eye(m_) + T / 2 * Xm) @ pw[j])
                Wt2 = unitary_from(bQ, pw2)
                KW2 = Wt2 @ K @ Wt2.conj().T
                lk2 = abs(np.vdot(K, V @ KW2 @ V.conj().T)) / D
                tk2 = abs(np.trace(K)) / D
                c2 = lk2 + 10.0 * max(0.0, tk2 - 0.05)
                if c2 < cur:
                    pw, Wt, cur = pw2, Wt2, c2
                else:
                    T *= 0.997
        KW = Wt @ K @ Wt.conj().T
        rec = {"restart": restart,
               "leak": round(float(abs(np.vdot(K, V @ KW @ V.conj().T)) / D),
                             5),
               "trK": round(float(abs(np.trace(K)) / D), 5)}
        if best is None or rec["leak"] < best["leak"]:
            best = rec
            print(json.dumps(rec), flush=True)
    print(json.dumps({"JOINT_FLOOR": best}), flush=True)
    with open("sl3_delta3_probe_v5.json", "w") as f:
        json.dump({"D0": float(D0), "best": best}, f, indent=1)
    print("PROBE-DONE", file=sys.stderr)


main()
