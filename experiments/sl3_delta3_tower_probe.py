#!/usr/bin/env python3
"""delta(3) probe: leak feasibility over SL_3(Z/8) on the natural
permutation representation (d = 512).

Minimize, over unitaries K, V in U(512),

  D(K, V) = sum_{c in LGENS} ||[K, rho(c)]||_2^2
          + sum_{(lam, philam) in PLIST} ||V rho(lam) V* - rho(philam)||_2^2
          + MU * |<VKV*, K>|^2    (leak penalty: forces orthogonality)
          + NU * |tr K|^2,

with rho the permutation action on (Z/8)^3.  A control run drops the
leak penalty (MU = 0) to expose the intertwining-only floor; the
quantity of interest is the GAP between the two minima.  Fixed
constraint lists per the two-primary-tower node: the enemy owes
vanishing defect only on fixed relators.
"""
import json
import sys

import numpy as np

MOD = 8
D = MOD ** 3
rng = np.random.default_rng(88)


def mat(a, b, c, d_, e, f, g, h, i):
    return np.array([[a, b, c], [d_, e, f], [g, h, i]], dtype=np.int64)


def e12(x):
    return mat(1, x, 0, 0, 1, 0, 0, 0, 1)


def e13(x):
    return mat(1, 0, x, 0, 1, 0, 0, 0, 1)


def e23(x):
    return mat(1, 0, 0, 0, 1, x, 0, 0, 1)


def e21(x):
    return mat(1, 0, 0, x, 1, 0, 0, 0, 1)


def e31(x):
    return mat(1, 0, 0, 0, 1, 0, x, 0, 1)


def e32(x):
    return mat(1, 0, 0, 0, 1, 0, 0, x, 1)


def perm_of(g):
    """Permutation sigma with rho(g) e_x = e_{g x mod 8}: returns array
    p with p[x_index] = (g x)_index."""
    p = np.empty(D, dtype=np.int64)
    for x0 in range(MOD):
        for x1 in range(MOD):
            for x2 in range(MOD):
                v = (g @ np.array([x0, x1, x2])) % MOD
                p[x0 * 64 + x1 * 8 + x2] = v[0] * 64 + v[1] * 8 + v[2]
    return p


# rho(g) as matrix: rho[p[j], j] = 1.  For products use index ops:
#   (M @ rho(g))[:, j] = M[:, p[j]]  -> M[:, p]
#   (rho(g) @ M)[i, :] = M[inv(p)[i], :] -> M[pinv, :]
def inv_perm(p):
    q = np.empty_like(p)
    q[p] = np.arange(len(p))
    return q


LGENS = [e12(1), e21(1), e13(1), e31(1), e23(1), e32(1)]
PLIST = [(e12(2), e12(1)), (e13(4), e13(1)), (e23(2), e23(1)),
         (e21(1), e21(2)), (e31(1), e31(4)), (e32(1), e32(2))]

LP = [perm_of(g) for g in LGENS]
PP = [(perm_of(a), perm_of(b)) for a, b in PLIST]
LPI = [inv_perm(p) for p in LP]
PPI = [(inv_perm(pa), inv_perm(pb)) for pa, pb in PP]


def comm_term(K, p, pinv):
    # g = Re tr(K rho K* rho*) / D ; defect = 2 - 2 g
    A = K[:, p]                      # K rho
    B = K[pinv, :]                   # rho K  -> (rho K)
    t = np.vdot(B, A) / D            # tr((rho K)^* (K rho)) = tr(K* rho* K rho)
    M = A @ B.conj().T               # K rho K* rho*  (via (rho K)^* = K* rho*)
    return t, M


def defect_and_grads(K, V, mu, nu):
    d = 0.0
    GK = np.zeros((D, D), dtype=complex)
    GV = np.zeros((D, D), dtype=complex)
    for p, pinv in zip(LP, LPI):
        t, M = comm_term(K, p, pinv)
        d += 2 - 2 * abs(t) ** 2
        G = np.conj(t) * (M - M.conj().T) / D
        GK += G - G.conj().T
    for (pa, pb), (pai, pbi) in zip(PP, PPI):
        A = V[:, pa]                 # V rho(lam)
        W = A @ V.conj().T           # V rho(lam) V*
        tt = np.trace(W[pbi, :]) / D  # tr(rho(philam)* W)
        d += 2 - 2 * np.real(tt)
        M = W[pbi, :]                # rho(philam)* W  (row perm)
        G = (M - M.conj().T) / D
        GV += G - G.conj().T
    if mu > 0:
        A = V @ K @ V.conj().T
        t = np.vdot(K, A) / D        # tr(K* V K V*) / D
        d += mu * abs(t) ** 2
        MV = A @ K.conj().T - K.conj().T @ A
        G = -mu * np.conj(t) * MV.conj().T / D
        GV += G - G.conj().T
        MK = V.conj().T @ K @ V
        MK2 = K @ MK.conj().T - MK.conj().T @ K
        G = -mu * np.conj(t) * MK2.conj().T / D
        GK += G - G.conj().T
    if nu > 0:
        t = np.trace(K) / D
        d += nu * abs(t) ** 2
        G = -nu * np.conj(t) * K.conj().T / D
        GK += G - G.conj().T
    return d, GK, GV


def retract(U, X, s):
    A = s * X
    return np.linalg.qr((np.eye(D) + A) @ U)[0]


def run(mu, nu, iters, restarts):
    best = None
    for r in range(restarts):
        K = np.linalg.qr(rng.normal(size=(D, D)) +
                         1j * rng.normal(size=(D, D)))[0]
        V = np.linalg.qr(rng.normal(size=(D, D)) +
                         1j * rng.normal(size=(D, D)))[0]
        step = 0.3
        dprev = None
        for it in range(iters):
            d, GK, GV = defect_and_grads(K, V, mu, nu)
            n = max(np.linalg.norm(GK), np.linalg.norm(GV), 1e-14)
            K2 = retract(K, -GK / n, step)
            V2 = retract(V, -GV / n, step)
            d2, _, _ = defect_and_grads(K2, V2, 0 * mu, 0 * nu)
            d2full, _, _ = defect_and_grads(K2, V2, mu, nu)
            if d2full < d:
                K, V = K2, V2
                step = min(step * 1.15, 0.6)
                if dprev is not None and dprev - d2full < 1e-8:
                    break
                dprev = d2full
            else:
                step *= 0.5
                if step < 1e-7:
                    break
        d, _, _ = defect_and_grads(K, V, 0, 0)
        A = V @ K @ V.conj().T
        leak = abs(np.vdot(K, A)) / D
        trk = abs(np.trace(K)) / D
        tot = d + (mu * leak ** 2 if mu else 0) + (nu * trk ** 2 if nu else 0)
        rec = {"restart": r, "raw_defect": round(float(d), 5),
               "leak_corr": round(float(leak), 5),
               "abs_tr_K": round(float(trk), 5)}
        print(json.dumps(rec), flush=True)
        if best is None or d < best["raw_defect"]:
            best = rec
    return best


def main():
    out = {}
    print("== control (no leak penalty) ==", flush=True)
    out["control"] = run(mu=0.0, nu=50.0, iters=140, restarts=3)
    print("== with leak penalty ==", flush=True)
    out["leak"] = run(mu=200.0, nu=50.0, iters=140, restarts=3)
    with open("sl3_delta3_tower_probe.json", "w") as f:
        json.dump(out, f, indent=1)
    print("PROBE-DONE", file=sys.stderr)


if __name__ == "__main__":
    main()
