#!/usr/bin/env python3
"""delta(3) probe v2: validated gradients + exact spectral floor.

Changes vs v1 (which stalled at ~23.5/24): gradients re-derived and
finite-difference-validated in-script on the SL_3(Z/2) toy (d = 8)
before the big run; the exact per-pair spectral floor (squared OT
distance between eigenvalue multisets, Hoffman--Wielandt) is computed
and subtracted, so the reported quantity is the beyond-spectral
defect.  Config: SL_3(Z/8) permutation action on (Z/8)^3, d = 512.
"""
import json
import sys

import numpy as np
from scipy.optimize import linear_sum_assignment

rng = np.random.default_rng(777)


def mats(mod):
    def m(*r):
        return np.array(r, dtype=np.int64).reshape(3, 3) % mod
    E = {}
    E['e12'] = lambda x: m(1, x, 0, 0, 1, 0, 0, 0, 1)
    E['e13'] = lambda x: m(1, 0, x, 0, 1, 0, 0, 0, 1)
    E['e23'] = lambda x: m(1, 0, 0, 0, 1, x, 0, 0, 1)
    E['e21'] = lambda x: m(1, 0, 0, x, 1, 0, 0, 0, 1)
    E['e31'] = lambda x: m(1, 0, 0, 0, 1, 0, x, 0, 1)
    E['e32'] = lambda x: m(1, 0, 0, 0, 1, 0, 0, x, 1)
    return E


def perm_of(g, mod):
    n = mod ** 3
    p = np.empty(n, dtype=np.int64)
    for x0 in range(mod):
        for x1 in range(mod):
            for x2 in range(mod):
                v = (g @ np.array([x0, x1, x2])) % mod
                p[(x0 * mod + x1) * mod + x2] = (v[0] * mod + v[1]) * mod + v[2]
    return p


def inv_perm(p):
    q = np.empty_like(p)
    q[p] = np.arange(len(p))
    return q


def build(mod, plist_spec, lgens_spec):
    E = mats(mod)
    lg = [perm_of(E[k](x), mod) for k, x in lgens_spec]
    pl = [(perm_of(E[k](x), mod), perm_of(E[k](y), mod))
          for k, x, y in plist_spec]
    return lg, pl


def perm_eigs(p):
    """Eigenvalue list of the permutation matrix (roots of unity per cycle)."""
    n = len(p)
    seen = np.zeros(n, dtype=bool)
    ev = []
    for i in range(n):
        if seen[i]:
            continue
        j, L = i, 0
        while not seen[j]:
            seen[j] = True
            j = p[j]
            L += 1
        ev.extend(np.exp(2j * np.pi * np.arange(L) / L))
    return np.array(ev)


def spectral_floor(pa, pb):
    ea, eb = perm_eigs(pa), perm_eigs(pb)
    C = np.abs(ea[:, None] - eb[None, :]) ** 2
    r, c = linear_sum_assignment(C)
    return C[r, c].sum() / len(ea)


def cayley(X, s, U):
    n = U.shape[0]
    A = (s / 2.0) * X
    return np.linalg.solve(np.eye(n) - A, (np.eye(n) + A) @ U)


# ---- energy and gradients (validated) ----
def term_comm(K, p, pinv):
    A = K[:, p]
    Bc = K[pinv, :]
    t = np.vdot(Bc, A) / K.shape[0]
    return t, A, Bc


def full_grad(K, V, lg, lgi, pl, pli, mu, nu):
    Dn = K.shape[0]
    f = 0.0
    NK = np.zeros_like(K)
    NV = np.zeros_like(V)
    for p, pinv in zip(lg, lgi):
        t, A, Bc = term_comm(K, p, pinv)
        f += 2 - 2 * abs(t) ** 2
        M = A @ Bc.conj().T                    # K rho K* rho*
        Mt = K[p, :][:, p] @ K.conj().T        # (rho* K rho) K*
        NK += -(4.0 / Dn) * np.conj(t) * (M - Mt)
    for (pa, pb), (pai, pbi) in zip(pl, pli):
        W = V[:, pa] @ V.conj().T              # V rho_a V*
        s = np.trace(W[pbi, :]) / Dn
        f += 2 - 2 * np.real(s)
        NV += -(2.0 / Dn) * (W[:, pbi] - W[pb, :])   # W B† - B† W
    if mu > 0:
        A2 = V @ K @ V.conj().T
        q = np.vdot(K, A2) / Dn
        f += mu * abs(q) ** 2
        NV += (2.0 * mu / Dn) * np.conj(q) * (A2 @ K.conj().T -
                                              K.conj().T @ A2)
        B2 = V.conj().T @ K @ V
        NK += (2.0 * mu / Dn) * np.conj(q) * (K @ B2.conj().T -
                                              A2 @ K.conj().T)
    if nu > 0:
        tr = np.trace(K) / Dn
        f += nu * abs(tr) ** 2
        NK += (2.0 * nu / Dn) * np.conj(tr) * K
    YK = (NK - NK.conj().T) / 2.0
    YV = (NV - NV.conj().T) / 2.0
    return f, YK, YV


def energy_only(K, V, lg, lgi, pl, pli, mu, nu):
    f, _, _ = full_grad(K, V, lg, lgi, pl, pli, mu, nu)
    return f


def fd_check():
    mod = 2
    lg_spec = [('e12', 1), ('e21', 1), ('e32', 1)]
    pl_spec = [('e12', 1, 1), ('e21', 1, 1)]
    lg, pl = build(mod, pl_spec, lg_spec)
    lgi = [inv_perm(p) for p in lg]
    pli = [(inv_perm(a), inv_perm(b)) for a, b in pl]
    n = mod ** 3
    K = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))[0]
    V = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))[0]
    ok = True
    # pure trace-term isolation
    f0t, YKt, _ = full_grad(K, V, [], [], [], [], 0.0, 2.0)
    for _ in range(3):
        Z = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
        X = (Z - Z.conj().T) / 2.0
        X /= np.linalg.norm(X)
        h = 1e-6
        K2 = cayley(X, h, K)
        f1t = energy_only(K2, V, [], [], [], [], 0.0, 2.0)
        num = (f1t - f0t) / h
        ana = -1.0 * np.real(np.vdot(X, YKt))
        print(f"PURETRACE num={num:.8f} ana={ana:.8f}", flush=True)
    for MU, NU in ((0.0, 0.0), (3.0, 0.0), (0.0, 2.0), (3.0, 2.0)):
      f0, YK, YV = full_grad(K, V, lg, lgi, pl, pli, MU, NU)
      for _ in range(6):
        Z = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
        X = (Z - Z.conj().T) / 2.0
        X /= np.linalg.norm(X)
        h = 1e-6
        for which in ('K', 'V'):
            if which == 'K':
                K2 = cayley(X, h, K)
                f1 = energy_only(K2, V, lg, lgi, pl, pli, MU, NU)
                Y = YK
            else:
                V2 = cayley(X, h, V)
                f1 = energy_only(K, V2, lg, lgi, pl, pli, MU, NU)
                Y = YV
            num = (f1 - f0) / h
            # descent direction Y: df along X is Re Tr(X N) = -<X, Y>*2?
            ana = -1.0 * np.real(np.vdot(X, Y))
            if abs(num - ana) > 5e-3 * max(1.0, abs(num)):
                print(f"FD-FAIL {which} mu={MU} nu={NU}: "
                      f"num={num:.6f} ana={ana:.6f}", flush=True)
                ok = False
    print("FD-CHECK", "PASS" if ok else "FAIL", flush=True)
    return ok


def main():
    if not fd_check():
        sys.exit(2)
    mod = 8
    lg_spec = [('e12', 1), ('e21', 1), ('e13', 1),
               ('e31', 1), ('e23', 1), ('e32', 1)]
    pl_spec = [('e12', 2, 1), ('e13', 4, 1), ('e23', 2, 1),
               ('e21', 1, 2), ('e31', 1, 4), ('e32', 1, 2)]
    lg, pl = build(mod, pl_spec, lg_spec)
    lgi = [inv_perm(p) for p in lg]
    pli = [(inv_perm(a), inv_perm(b)) for a, b in pl]
    floor = sum(spectral_floor(a, b) for a, b in pl)
    print(json.dumps({"spectral_floor_total": round(float(floor), 5)}),
          flush=True)
    n = mod ** 3
    out = {"floor": floor, "runs": []}
    for mu in (0.0, 300.0):
        for r in range(2):
            K = np.linalg.qr(rng.normal(size=(n, n)) +
                             1j * rng.normal(size=(n, n)))[0]
            V = np.linalg.qr(rng.normal(size=(n, n)) +
                             1j * rng.normal(size=(n, n)))[0]
            step = 0.5
            fprev = None
            for it in range(240):
                f, YK, YV = full_grad(K, V, lg, lgi, pl, pli, mu, 50.0)
                nn = max(np.linalg.norm(YK), np.linalg.norm(YV), 1e-14)
                K2 = cayley(YK / nn, step, K)
                V2 = cayley(YV / nn, step, V)
                f2 = energy_only(K2, V2, lg, lgi, pl, pli, mu, 50.0)
                if f2 < f:
                    K, V = K2, V2
                    step = min(step * 1.2, 1.0)
                    if fprev is not None and fprev - f2 < 1e-7:
                        break
                    fprev = f2
                else:
                    step *= 0.5
                    if step < 1e-7:
                        break
            fr = energy_only(K, V, lg, lgi, pl, pli, 0.0, 0.0)
            A2 = V @ K @ V.conj().T
            leak = abs(np.vdot(K, A2)) / n
            rec = {"mu": mu, "restart": r,
                   "raw_defect": round(float(fr), 5),
                   "beyond_spectral": round(float(fr - floor), 5),
                   "leak_corr": round(float(leak), 5),
                   "abs_trK": round(float(abs(np.trace(K)) / n), 5)}
            print(json.dumps(rec), flush=True)
            out["runs"].append(rec)
    with open("sl3_delta3_tower_probe_v2.json", "w") as fjs:
        json.dump(out, fjs, indent=1)
    print("PROBE-DONE", file=sys.stderr)


if __name__ == "__main__":
    main()
