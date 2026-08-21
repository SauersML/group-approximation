#!/usr/bin/env python3
"""v4-lite: exact block-unitary K in Z, global multistart floor.

Z = rho(G)' (37-dim) decomposes as ⊕ M_{m} blocks; extract the block
structure via eigenprojections of a generic element, parametrize K
exactly as a product of small unitaries (exponential map per block),
and minimize |<Phi(K), K>| over many restarts at the control-optimal
dictionary V, with |tau(K)| <= 0.05 enforced by penalty.  Reports the
global-confidence floor of the prototype at fixed V, then re-optimizes
V against the found K to test V-side escape.
"""
import json
import sys

import numpy as np

exec(open("sl3_delta3_probe_v3.py").read().split("def main()")[0])


def main():
    NOR, LAB = orbit_reps()
    mats = [(LAB == i).astype(np.float64) for i in range(NOR)]
    osize = np.array([m_.sum() for m_ in mats])
    pl = [(perm_of(a), perm_of(b)) for a, b in PLIST]
    pli = [(inv_perm(a), inv_perm(b)) for a, b in pl]

    def defect_V(V):
        f = 0.0
        for (pa, pb), (pai, pbi) in zip(pl, pli):
            W = V[:, pa] @ V.conj().T
            f += 2 - 2 * np.real(np.trace(W[pbi, :]) / D)
        return f

    # control-optimal V (as in phi-spectrum run)
    rng2 = np.random.default_rng(777)
    V = np.linalg.qr(rng2.normal(size=(D, D)) +
                     1j * rng2.normal(size=(D, D)))[0]
    step = 0.5
    for it in range(260):
        f0 = defect_V(V)
        NV = np.zeros((D, D), dtype=complex)
        for (pa, pb), (pai, pbi) in zip(pl, pli):
            W = V[:, pa] @ V.conj().T
            NV += -(2.0 / D) * (W[:, pbi] - W[pb, :])
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
    print(json.dumps({"D0": round(float(D0), 5)}), flush=True)

    # block structure of Z via generic element
    rngA = np.random.default_rng(4242)
    A = np.zeros((D, D))
    for i in range(NOR):
        A += rngA.normal() * mats[i]
    A = (A + A.T) / 2.0
    ev, U = np.linalg.eigh(A)
    clusters = []
    start = 0
    for i in range(1, D + 1):
        if i == D or abs(ev[i] - ev[i - 1]) > 1e-7:
            clusters.append((start, i))
            start = i
    # group clusters into isotypic blocks: same dim AND K-block joint:
    # two clusters belong to the same irrep-block iff some E_i maps one
    # to the other; detect by testing overlap through a second generic
    # element's off-diagonal blocks.
    B2 = np.zeros((D, D))
    for i in range(NOR):
        B2 += rngA.normal() * mats[i]
    B2 = (B2 + B2.T) / 2.0
    ncl = len(clusters)
    adj = np.zeros((ncl, ncl), dtype=bool)
    for a_ in range(ncl):
        s0, s1 = clusters[a_]
        for b_ in range(a_ + 1, ncl):
            t0, t1 = clusters[b_]
            if (s1 - s0) != (t1 - t0):
                continue
            blk = U[:, s0:s1].T @ B2 @ U[:, t0:t1]
            if np.linalg.norm(blk) > 1e-6:
                adj[a_, b_] = adj[b_, a_] = True
    # connected components = irrep blocks; component size = multiplicity
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
            for y in range(ncl):
                if adj[x, y] and comp[y] < 0:
                    stack.append(y)
        nc += 1
    blocks = {}
    for i, c_ in enumerate(comp):
        blocks.setdefault(c_, []).append(i)
    profile = sorted((len(v), clusters[v[0]][1] - clusters[v[0]][0])
                     for v in blocks.values())
    print(json.dumps({"blocks_mult_dim": profile}), flush=True)

    # basis W: for each block, isometries onto each cluster copy
    binfo = []
    for c_, cl in blocks.items():
        iso = [U[:, clusters[k][0]:clusters[k][1]] for k in cl]
        binfo.append(iso)

    def K_from_params(params):
        K = np.zeros((D, D), dtype=complex)
        idx = 0
        for iso in binfo:
            m_ = len(iso)
            X = params[idx]
            idx += 1
            # X: m x m unitary; K += sum_{ab} X[a,b] iso_a iso_b^*
            for a_ in range(m_):
                for b_ in range(m_):
                    if abs(X[a_, b_]) > 1e-12:
                        K += X[a_, b_] * (iso[a_] @ iso[b_].conj().T)
        return K

    def rand_unitaries(rngu):
        ps = []
        for iso in binfo:
            m_ = len(iso)
            Zm = rngu.normal(size=(m_, m_)) + 1j * rngu.normal(size=(m_, m_))
            ps.append(np.linalg.qr(Zm)[0])
        return ps

    rngu = np.random.default_rng(99)
    best = None
    for restart in range(60):
        ps = rand_unitaries(rngu)
        # local refinement: random small unitary moves per block
        K = K_from_params(ps)
        lk = abs(np.vdot(K, V @ K @ V.conj().T)) / D
        tk = abs(np.trace(K)) / D
        cur = lk + 10.0 * max(0.0, tk - 0.05)
        T = 0.3
        for it in range(400):
            j = rngu.integers(0, len(ps))
            m_ = ps[j].shape[0]
            Zm = rngu.normal(size=(m_, m_)) + 1j * rngu.normal(size=(m_, m_))
            Xm = (Zm - Zm.conj().T) / 2
            ps2 = [p.copy() for p in ps]
            ps2[j] = np.linalg.solve(np.eye(m_) - T / 2 * Xm,
                                     (np.eye(m_) + T / 2 * Xm) @ ps[j])
            K2 = K_from_params(ps2)
            lk2 = abs(np.vdot(K2, V @ K2 @ V.conj().T)) / D
            tk2 = abs(np.trace(K2)) / D
            c2 = lk2 + 10.0 * max(0.0, tk2 - 0.05)
            if c2 < cur:
                ps, cur = ps2, c2
                K = K2
            else:
                T *= 0.995
        K = K_from_params(ps)
        rec = {"restart": restart,
               "leak": round(float(abs(np.vdot(K, V @ K @ V.conj().T)) / D), 5),
               "trK": round(float(abs(np.trace(K)) / D), 5),
               "unit_err": round(float(np.linalg.norm(
                   K.conj().T @ K - np.eye(D)) / np.sqrt(D)), 6)}
        if best is None or rec["leak"] < best["leak"]:
            best = rec
            print(json.dumps(rec), flush=True)
    print(json.dumps({"FLOOR_at_controlV": best}), flush=True)
    with open("sl3_delta3_probe_v4.json", "w") as f:
        json.dump({"D0": float(D0), "best": best,
                   "blocks": profile}, f, indent=1)
    print("PROBE-DONE", file=sys.stderr)


main()
