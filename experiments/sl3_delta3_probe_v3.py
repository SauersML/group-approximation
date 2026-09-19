#!/usr/bin/env python3
"""delta(3) probe v3: K exactly in the 37-dim witness algebra.

K = sum_i c_i A_i over the G-orbit matrices (exact commutant element),
with unitarity enforced by penalty ||K*K - 1||_2^2; V free in U(512).
Phase 1: minimize dictionary defect alone -> D0 (control).
Phase 2: minimize |<VKV*,K>|^2 + LAM*max(0, defect - D0 - SLACK)^2
         -> measures leak_min at defect budget D0 + SLACK.
Reports the tradeoff at SLACK in {0.5, 1.0, 2.0}.
"""
import json
import sys

import numpy as np

MOD = 8
D = MOD ** 3
rng = np.random.default_rng(1234)


def m(*r):
    return [list(r[0:3]), list(r[3:6]), list(r[6:9])]


def perm_of(g):
    p = np.empty(D, dtype=np.int64)
    for x0 in range(MOD):
        for x1 in range(MOD):
            for x2 in range(MOD):
                v0 = (g[0][0]*x0+g[0][1]*x1+g[0][2]*x2) % MOD
                v1 = (g[1][0]*x0+g[1][1]*x1+g[1][2]*x2) % MOD
                v2 = (g[2][0]*x0+g[2][1]*x1+g[2][2]*x2) % MOD
                p[(x0*MOD+x1)*MOD+x2] = (v0*MOD+v1)*MOD+v2
    return p


def inv_perm(p):
    q = np.empty_like(p)
    q[p] = np.arange(len(p))
    return q


GENS_G = [m(1,1,0,0,1,0,0,0,1), m(1,0,0,1,1,0,0,0,1),
          m(1,0,1,0,1,0,0,0,1), m(1,0,0,0,1,0,1,0,1),
          m(1,0,0,0,1,1,0,0,1), m(1,0,0,0,1,0,0,1,1)]
PLIST = [(m(1,2,0,0,1,0,0,0,1), m(1,1,0,0,1,0,0,0,1)),
         (m(1,0,4,0,1,0,0,0,1), m(1,0,1,0,1,0,0,0,1)),
         (m(1,0,0,0,1,2,0,0,1), m(1,0,0,0,1,1,0,0,1)),
         (m(1,0,0,1,1,0,0,0,1), m(1,0,0,2,1,0,0,0,1)),
         (m(1,0,0,0,1,0,1,0,1), m(1,0,0,0,1,0,4,0,1)),
         (m(1,0,0,0,1,0,0,1,1), m(1,0,0,0,1,0,0,2,1))]


def orbit_reps():
    """Labels of G-orbits on X x X via union-find (as before)."""
    perms = [perm_of(g) for g in GENS_G]
    n = D * D
    parent = np.arange(n, dtype=np.int64)

    def find(a):
        root = a
        while parent[root] != root:
            root = parent[root]
        while parent[a] != root:
            parent[a], a = root, parent[a]
        return root

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


def main():
    NOR, LAB = orbit_reps()
    print(json.dumps({"orbits": int(NOR)}), flush=True)
    # orbit matrices, L2-normalized so K = sum c_i E_i with real coeff grads
    mats = []
    for i in range(NOR):
        Mi = (LAB == i).astype(np.float64)
        mats.append(Mi)
    pl = [(perm_of(a), perm_of(b)) for a, b in PLIST]
    pli = [(inv_perm(a), inv_perm(b)) for a, b in pl]

    def build_K(cvec):
        K = np.zeros((D, D), dtype=complex)
        for i in range(NOR):
            K += cvec[i] * mats[i]
        return K

    def defect_V(V):
        f = 0.0
        for (pa, pb), (pai, pbi) in zip(pl, pli):
            W = V[:, pa] @ V.conj().T
            f += 2 - 2 * np.real(np.trace(W[pbi, :]) / D)
        return f

    def unit_pen(K):
        E = K.conj().T @ K - np.eye(D)
        return np.real(np.vdot(E, E)) / D

    def leak(K, V):
        A2 = V @ K @ V.conj().T
        return abs(np.vdot(K, A2)) / D

    # Phase 1: control defect via gradient descent on V only
    V = np.linalg.qr(rng.normal(size=(D, D)) + 1j*rng.normal(size=(D, D)))[0]
    step = 0.5
    for it in range(200):
        f0 = defect_V(V)
        NV = np.zeros((D, D), dtype=complex)
        for (pa, pb), (pai, pbi) in zip(pl, pli):
            W = V[:, pa] @ V.conj().T
            NV += -(2.0 / D) * (W[:, pbi] - W[pb, :])
        Y = (NV - NV.conj().T) / 2.0
        nn = max(np.linalg.norm(Y), 1e-14)
        A = (step / nn) * Y
        V2 = np.linalg.solve(np.eye(D) - A/2, (np.eye(D) + A/2) @ V)
        f2 = defect_V(V2)
        if f2 < f0:
            V = V2
            step = min(step*1.2, 1.0)
        else:
            step *= 0.5
            if step < 1e-7:
                break
    D0 = defect_V(V)
    print(json.dumps({"phase1_control_defect": round(float(D0), 5)}),
          flush=True)

    # precompute association-scheme structure: products E_i E_j in basis
    print(json.dumps({"precompute": "structure constants"}), flush=True)
    reps = []
    seenrep = {}
    for x in range(D):
        for y in range(D):
            l = int(LAB[x, y])
            if l not in seenrep:
                seenrep[l] = (x, y)
            if len(seenrep) == NOR:
                break
        if len(seenrep) == NOR:
            break
    S = np.zeros((NOR, NOR, NOR))
    for i in range(NOR):
        Mi = mats[i]
        for j in range(NOR):
            P = Mi @ mats[j]
            for k in range(NOR):
                x, y = seenrep[k]
                S[i, j, k] = P[x, y]
    # adjoint orbit: E_i^T = E_{it[i]}
    it = np.empty(NOR, dtype=np.int64)
    for i in range(NOR):
        x, y = seenrep[i]
        it[i] = int(LAB[y, x])
    osize = np.array([mats[i].sum() for i in range(NOR)])
    diagmask = np.array([1.0 if LAB[0, 0] == i or
                         (mats[i] * np.eye(D)).sum() > 0 else 0.0
                         for i in range(NOR)])
    trE = np.array([(mats[i] * np.eye(D)).sum() for i in range(NOR)])

    def Kmat(c):
        K = np.zeros((D, D), dtype=complex)
        for i in range(NOR):
            K += c[i] * mats[i]
        return K

    def unit_quartic(c):
        # K*K = sum_{i,j} conj(c_it[i]) ... K* = sum conj(c_i) E_{it[i]}
        # d_k = sum_{i,j} conj(c_i) c_j S[it[i], j, k]; want d = e_id
        dvec = np.zeros(NOR, dtype=complex)
        for i in range(NOR):
            ci = np.conj(c[i])
            dvec += ci * (S[it[i]] .T @ c)
        # identity element in basis: orbit of (x,x) classes: identity
        # matrix = sum over diagonal orbits with coefficient 1
        target = trE / np.maximum(osize, 1)  # 1 on diagonal orbits
        r = dvec - target
        # ||K*K - 1||_2^2 / D = sum_k |r_k|^2 * osize_k / D
        val = float(np.sum(np.abs(r) ** 2 * osize) / D)
        grad = np.zeros(NOR, dtype=complex)
        for i in range(NOR):
            # d dvec/d conj(c_i) = S[it[i]].T @ c
            grad[i] += np.sum(np.conj(r) * (S[it[i]].T @ c) * osize) / D
        # plus term from c in dvec: d dvec_k / d c_j = sum_i conj(c_i) S[it[i], j, k]
        T = np.zeros((NOR, NOR), dtype=complex)
        for i in range(NOR):
            T += np.conj(c[i]) * S[it[i]]
        grad += (T.conj() @ (r * osize)) / D
        return val, grad

    out = {"orbits": int(NOR), "D0": float(D0), "runs": []}
    for SLACK in (0.5, 1.0, 2.0):
        for restart in range(2):
            c = (rng.normal(size=NOR) + 1j * rng.normal(size=NOR))
            K = Kmat(c)
            c *= np.sqrt(D) / np.linalg.norm(K)
            Vw = V.copy()
            LAM, MUU = 60.0, 300.0
            stepC, stepV = 0.1, 0.3
            Qf = None
            for itn in range(220):
                if itn % 4 == 0:
                    VE = [Vw[:, perm_of.__defaults__] if False else None]
                    Qf = np.zeros((NOR, NOR), dtype=complex)
                    K1 = None
                    VEj = []
                    for j in range(NOR):
                        VEj.append(Vw @ mats[j] @ Vw.conj().T)
                    for i in range(NOR):
                        for j in range(NOR):
                            Qf[i, j] = np.vdot(mats[i], VEj[j]) / D
                q = np.conj(c) @ (Qf @ c)
                uv, ug = unit_quartic(c)
                trk = np.sum(c * trE) / D
                F = abs(q) ** 2 + MUU * uv + 5.0 * abs(trk) ** 2
                gq = 2 * np.conj(q) * (Qf @ c)
                gc = gq + MUU * 2 * ug + 5.0 * 2 * np.conj(trk) * trE / D
                c2 = c - stepC * gc / max(np.linalg.norm(gc), 1e-12)
                q2 = np.conj(c2) @ (Qf @ c2)
                uv2, _ = unit_quartic(c2)
                trk2 = np.sum(c2 * trE) / D
                F2 = abs(q2) ** 2 + MUU * uv2 + 5.0 * abs(trk2) ** 2
                if F2 < F:
                    c = c2
                    stepC = min(stepC * 1.1, 0.3)
                else:
                    stepC *= 0.6
                # V-step every 4 iters
                if itn % 4 == 3:
                    K = Kmat(c)
                    A2 = Vw @ K @ Vw.conj().T
                    qq = np.vdot(K, A2) / D
                    NV = (2.0 / D) * np.conj(qq) * (A2 @ K.conj().T -
                                                    K.conj().T @ A2)
                    df = defect_V(Vw)
                    over = max(0.0, df - D0 - SLACK)
                    if over > 0:
                        for (pa, pb), (pai, pbi) in zip(pl, pli):
                            W = Vw[:, pa] @ Vw.conj().T
                            NV += -2 * LAM * over * (2.0 / D) *                                 (W[:, pbi] - W[pb, :])
                    Y = (NV - NV.conj().T) / 2.0
                    nn = max(np.linalg.norm(Y), 1e-14)
                    A = (stepV / nn) * Y
                    V2 = np.linalg.solve(np.eye(D) - A / 2,
                                         (np.eye(D) + A / 2) @ Vw)
                    l1 = abs(np.vdot(K, Vw @ K @ Vw.conj().T) / D) ** 2 +                         LAM * max(0.0, defect_V(Vw) - D0 - SLACK) ** 2
                    l2 = abs(np.vdot(K, V2 @ K @ V2.conj().T) / D) ** 2 +                         LAM * max(0.0, defect_V(V2) - D0 - SLACK) ** 2
                    if l2 < l1:
                        Vw = V2
                        stepV = min(stepV * 1.1, 0.6)
                    else:
                        stepV *= 0.6
            K = Kmat(c)
            A2 = Vw @ K @ Vw.conj().T
            rec = {"slack": SLACK, "restart": restart,
                   "leak": round(float(abs(np.vdot(K, A2)) / D), 5),
                   "unit_pen": round(float(unit_quartic(c)[0]), 6),
                   "defect": round(float(defect_V(Vw)), 4),
                   "trK": round(float(abs(np.sum(c * trE)) / D), 5)}
            print(json.dumps(rec), flush=True)
            out["runs"].append(rec)
    with open("sl3_delta3_probe_v3.json", "w") as f:
        json.dump(out, f, indent=1)
    print("PROBE-DONE", file=sys.stderr)


if __name__ == "__main__":
    main()
