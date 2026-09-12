#!/usr/bin/env python3
"""Even theta-constant projective representation of Sp_4(Z) (dimension 10), phases read off numerically."""
import json, itertools, numpy as np
from collections import Counter
pres = json.load(open("pres6.json")); GEN = [np.array(g, dtype=np.int64) for g in pres["generators"]]
rels = pres["relators"]; lifts = pres["lifts"]
def blocks(g): return g[:2,:2], g[:2,2:], g[2:,:2], g[2:,2:]
chars = list(itertools.product([0,1], repeat=4))
even = [m for m in chars if (m[0]*m[2] + m[1]*m[3]) % 2 == 0]
N = 7; lat = np.array(list(itertools.product(range(-N, N+1), repeat=2)), dtype=float)
def theta(m, tau):
    a = np.array(m[:2]) / 2.0; b = np.array(m[2:]) / 2.0
    v = lat + a
    q = np.einsum('ni,ij,nj->n', v, tau, v)
    return np.sum(np.exp(1j*np.pi*q + 2j*np.pi*(v @ b)))
def gtau(g, tau):
    A,B,C,D = [x.astype(complex) for x in blocks(g)]
    return (A @ tau + B) @ np.linalg.inv(C @ tau + D)
rng = np.random.default_rng(5)
def rand_tau():
    X = rng.normal(size=(2,2)); X = (X + X.T)/2 * 0.3
    Y = rng.normal(size=(2,2)); Y = Y @ Y.T * 0.2 + 0.9*np.eye(2)
    return X + 1j*Y
taus = [rand_tau() for _ in range(3)]
def monomial_for(g):
    T0 = [np.array([theta(m, t) for m in even]) for t in taus]
    T1 = [np.array([theta(n, gtau(g, t)) for n in even]) for t in taus]
    # ratios R[t][j,i] = theta[n_j](g tau_t)/theta[m_i](tau_t)
    R = [np.outer(T1[t], 1.0/T0[t]) for t in range(3)]
    # find i0,j0 and assignment i->j such that R[t][j,i]/R[t][j0,i0] is tau-independent and unimodular
    for i0 in range(10):
        for j0 in range(10):
            assign = {}
            ok = True
            for i in range(10):
                found = None
                for j in range(10):
                    q = [R[t][j, i] / R[t][j0, i0] for t in range(3)]
                    if abs(abs(q[0]) - 1) < 1e-5 and abs(q[0]-q[1]) < 1e-5 and abs(q[0]-q[2]) < 1e-5:
                        found = (j, q[0]); break
                if found is None: ok = False; break
                assign[i] = found
            if ok and len(set(j for j, _ in assign.values())) == 10:
                U = np.zeros((10, 10), dtype=complex)
                for i, (j, q) in assign.items(): U[j, i] = q / abs(q)
                return U
    raise RuntimeError("no consistent monomial structure")
R8 = [monomial_for(g) for g in GEN]
for U in R8: assert np.allclose(U @ U.conj().T, np.eye(10))
print("even theta-constant monomial matrices built for all 8 generators", flush=True)
M = R8 + [U.conj().T for U in R8]
test_idx = [i for i, k in enumerate(lifts) if k != 0] + list(rng.choice(len(rels), size=3000, replace=False))
lam = {}; bad = 0
for i in test_idx:
    P = np.eye(10, dtype=complex)
    for a in rels[i]: P = P @ M[a]
    if not np.allclose(P, P[0,0]*np.eye(10), atol=1e-5): bad += 1
    else: lam[i] = np.angle(P[0,0])
print(f"scalar on {len(lam)} of {len(test_idx)} tested relators (nonscalar {bad})", flush=True)
if bad == 0:
    ph8 = {i: int(round(l/(2*np.pi)*8)) % 8 for i, l in lam.items()}
    dev = max(abs(l/(2*np.pi)*8 - round(l/(2*np.pi)*8)) for l in lam.values())
    print("phases are 8th roots to within", f"{dev:.2e}", "; histogram:", sorted(Counter(ph8.values()).items()), flush=True)
    print("phases on lifted relators:", [ph8[i] for i, k in enumerate(lifts) if k != 0 and i in ph8], flush=True)
    def expsum(r):
        n = [0]*8
        for a in r: n[a % 8] += 1 if a < 8 else -1
        return n
    ES = {i: expsum(rels[i]) for i in ph8}
    grid = np.array(list(itertools.product(range(8), repeat=8)), dtype=np.int64)
    for name, target in [("metaplectic pattern (-1)^k", lambda i: (4*lifts[i]) % 8), ("genuine (all +1)", lambda i: 0)]:
        eqs = sorted(ph8.keys(), key=lambda i: sum(abs(x) for x in ES[i]))[:80]
        mask = np.ones(len(grid), dtype=bool)
        for i in eqs:
            n = np.array(ES[i]); b = (target(i) - ph8[i]) % 8
            mask &= ((grid @ n) % 8 == b)
        full = [tuple(int(v) for v in x) for x in grid[mask] if all((np.dot(ES[i], x) + ph8[i] - target(i)) % 8 == 0 for i in ph8)]
        print(f"rescaling by 8th roots to match {name}: {len(full)} solutions" + (f", e.g. {full[0]}" if full else ""), flush=True)
    np.save("theta10_generators.npy", np.stack(R8))
