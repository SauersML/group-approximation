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

    out = {"orbits": int(NOR), "D0": float(D0), "runs": []}
    for SLACK in (0.5, 1.0, 2.0):
        best = None
        for restart in range(2):
            c = rng.normal(size=NOR) + 1j*rng.normal(size=NOR)
            K = build_K(c)
            # normalize to near-unitary: scale so ||K||_2 ~ sqrt(D)
            K *= np.sqrt(D) / np.linalg.norm(K)
            c *= np.sqrt(D) / np.linalg.norm(build_K(np.ones(NOR)*0+c))
            Vw = V.copy()
            LAM, MUU = 50.0, 200.0
            stepC, stepV = 0.05, 0.3
            for it in range(300):
                K = build_K(c)
                lk = leak(K, Vw)
                up = unit_pen(K)
                df = defect_V(Vw)
                over = max(0.0, df - D0 - SLACK)
                F = lk**2 + MUU*up + LAM*over**2
                # numeric gradient in c (cheap: NOR dims)
                gc = np.zeros(NOR, dtype=complex)
                h = 1e-5
                for i in range(NOR):
                    for pha in (1.0, 1j):
                        c2 = c.copy()
                        c2[i] += h*pha
                        K2 = build_K(c2)
                        F2 = leak(K2, Vw)**2 + MUU*unit_pen(K2)
                        g = (F2 - (lk**2 + MUU*up)) / h
                        gc[i] += g * (pha.real - 1j*pha.imag if pha == 1j
                                      else 1.0) * (1.0 if pha == 1.0 else 1j)
                c2 = c - stepC * gc / max(np.linalg.norm(gc), 1e-12)
                K2 = build_K(c2)
                F2 = (leak(K2, Vw)**2 + MUU*unit_pen(K2) + LAM*over**2)
                if F2 < F:
                    c = c2
                else:
                    stepC *= 0.7
                # V-step on leak + defect-overrun
                A2 = Vw @ K @ Vw.conj().T
                q = np.vdot(K, A2) / D
                NV = (2.0/D)*np.conj(q)*(A2 @ K.conj().T - K.conj().T @ A2)
                if over > 0:
                    for (pa, pb), (pai, pbi) in zip(pl, pli):
                        W = Vw[:, pa] @ Vw.conj().T
                        NV += -2*LAM*over*(2.0/D)*(W[:, pbi] - W[pb, :])
                Y = (NV - NV.conj().T)/2.0
                nn = max(np.linalg.norm(Y), 1e-14)
                A = (stepV/nn)*Y
                V2 = np.linalg.solve(np.eye(D)-A/2, (np.eye(D)+A/2) @ Vw)
                lk2 = leak(build_K(c), V2)
                df2 = defect_V(V2)
                F2 = lk2**2 + MUU*unit_pen(build_K(c)) + \
                    LAM*max(0.0, df2-D0-SLACK)**2
                F1 = leak(build_K(c), Vw)**2 + MUU*unit_pen(build_K(c)) + \
                    LAM*max(0.0, defect_V(Vw)-D0-SLACK)**2
                if F2 < F1:
                    Vw = V2
                    stepV = min(stepV*1.1, 0.6)
                else:
                    stepV *= 0.6
            K = build_K(c)
            rec = {"slack": SLACK, "restart": restart,
                   "leak": round(float(leak(K, Vw)), 5),
                   "unit_pen": round(float(unit_pen(K)), 6),
                   "defect": round(float(defect_V(Vw)), 4),
                   "trK": round(float(abs(np.trace(K))/D), 5)}
            print(json.dumps(rec), flush=True)
            out["runs"].append(rec)
            if best is None or rec["leak"] < best:
                best = rec["leak"]
    with open("sl3_delta3_probe_v3.json", "w") as f:
        json.dump(out, f, indent=1)
    print("PROBE-DONE", file=sys.stderr)


if __name__ == "__main__":
    main()
