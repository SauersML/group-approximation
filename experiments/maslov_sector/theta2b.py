#!/usr/bin/env python3
"""Second-order theta constants Theta[a](tau) = theta[a,0](2 tau), a in (Z/2)^2: a 4-dimensional projective
representation of Sp_4(Z) read off numerically.  For each root generator g the 4x4 matrix M(g) is the unique
(up to scalar) solution of  Theta(g tau) parallel to M Theta(tau)  at several random Siegel points, found as the
null vector of the linear system of 2x2 minors.  Then M(g) is normalized to a unitary, the relators are checked
to be scalar, and the scalar phases are compared with the universal-cover lift pattern (-1)^k_r up to a
coboundary in the generator phases (a continuous 8-parameter fit, verified on all relators)."""
import json, itertools, sys, numpy as np
from scipy.optimize import minimize
pres = json.load(open("pres6.json")); GEN = [np.array(g, dtype=np.int64) for g in pres["generators"]]
rels = pres["relators"]; lifts = np.array(pres["lifts"])
def blocks(g): return g[:2,:2], g[:2,2:], g[2:,:2], g[2:,2:]
chars = [np.array(a, dtype=float) for a in itertools.product([0,1], repeat=2)]
N = 8; lat = np.array(list(itertools.product(range(-N, N+1), repeat=2)), dtype=float)
def Theta(a, tau):
    v = lat + a/2.0
    q = np.einsum('ni,ij,nj->n', v, 2*tau, v)
    return np.sum(np.exp(1j*np.pi*q))
def vec(tau): return np.array([Theta(a, tau) for a in chars])
def gtau(g, tau):
    A,B,C,D = [x.astype(complex) for x in blocks(g)]
    return (A @ tau + B) @ np.linalg.inv(C @ tau + D)
rng = np.random.default_rng(11)
def rand_tau():
    X = rng.normal(size=(2,2)); X = (X + X.T)/2 * 0.3
    Y = rng.normal(size=(2,2)); Y = Y @ Y.T * 0.2 + 1.0*np.eye(2)
    return X + 1j*Y
taus = [rand_tau() for _ in range(8)]
def solve_M(g):
    rows = []
    for t in taus:
        v = vec(t); w = vec(gtau(g, t))
        # unknown M as 16-vector m[4*a+b]; (Mv)_a = sum_b M[a,b] v[b]
        for a in range(4):
            for b in range(a+1, 4):
                row = np.zeros(16, dtype=complex)
                row[4*a:4*a+4] += w[b]*v      # (Mv)_a w_b
                row[4*b:4*b+4] -= w[a]*v      # - (Mv)_b w_a
                rows.append(row)
    A = np.array(rows); _, s, Vh = np.linalg.svd(A)
    M = Vh[-1].conj().reshape(4,4)
    M = M * (2.0/np.linalg.norm(M))
    return M, s[-2]/s[0], s[-1]/s[0]
Ms = []
for i, g in enumerate(GEN):
    M, s2, s1 = solve_M(g)
    unit = np.linalg.norm(M @ M.conj().T - np.eye(4))
    print(f"generator {i}: singular ratios second-smallest {s2:.2e} smallest {s1:.2e}; unitarity residual {unit:.2e}", flush=True)
    W, _, Vh = np.linalg.svd(M); M = W @ Vh   # polar unitary part
    Ms.append(M)
Ms = np.stack(Ms); np.save("theta4_generators.npy", Ms)
Mall = np.concatenate([Ms, np.conj(np.transpose(Ms, (0,2,1)))])
# relator check on all relators, batched by length
byl = {}
for i, r in enumerate(rels): byl.setdefault(len(r), []).append(i)
lam = np.zeros(len(rels), dtype=complex); nonscalar = 0; maxns = 0.0
for ell, idx in sorted(byl.items()):
    W_ = np.array([rels[i] for i in idx]); n = len(idx)
    P = np.broadcast_to(np.eye(4, dtype=complex), (n, 4, 4)).copy()
    for p in range(ell): P = P @ Mall[W_[:, p]]
    c = np.einsum('nii->n', P)/4
    D = P - c[:, None, None]*np.eye(4)
    ns = np.sqrt(np.real(np.einsum('nij,nij->n', np.conj(D), D))/4)
    maxns = max(maxns, float(ns.max())); nonscalar += int((ns > 1e-4).sum())
    lam[idx] = c/np.abs(c)
print(f"relators: {len(rels)}; nonscalar {nonscalar}; max nonscalar defect {maxns:.2e}", flush=True)
# exponent sums
E = np.zeros((len(rels), 8))
for i, r in enumerate(rels):
    for x in r: E[i, x % 8] += 1 if x < 8 else -1
target = (-1.0)**lifts
mu = lam / target   # want mu_r = exp(i n(r).theta) for some theta
def cost(th, idx):
    return np.sum(np.abs(mu[idx]*np.exp(-1j*(E[idx] @ th)) - 1)**2)
sub = rng.choice(len(rels), size=4000, replace=False)
best = None
for trial in range(60):
    th0 = rng.uniform(0, 2*np.pi, size=8)
    res = minimize(cost, th0, args=(sub,), method="BFGS")
    if best is None or res.fun < best.fun: best = res
th = best.x
resid = np.abs(mu*np.exp(-1j*(E @ th)) - 1)
print(f"coboundary fit to (-1)^k: max residual over all relators {resid.max():.2e} (mean {resid.mean():.2e}); phases theta/2pi = {np.round(th/(2*np.pi) % 1, 4)}", flush=True)
# also test against the trivial class (are the phases a coboundary of the trivial pattern?)
mu0 = lam.copy()
def cost0(th, idx): return np.sum(np.abs(mu0[idx]*np.exp(-1j*(E[idx] @ th)) - 1)**2)
best0 = None
for trial in range(60):
    res = minimize(cost0, rng.uniform(0, 2*np.pi, size=8), args=(sub,), method="BFGS")
    if best0 is None or res.fun < best0.fun: best0 = res
resid0 = np.abs(mu0*np.exp(-1j*(E @ best0.x)) - 1)
print(f"coboundary fit to the trivial class: max residual {resid0.max():.2e}", flush=True)
if resid.max() < 1e-3:
    R = np.stack([np.exp(-1j*th[s])*Ms[s] for s in range(8)])
    # verify exactly
    Rall = np.concatenate([R, np.conj(np.transpose(R, (0,2,1)))]); worst = 0.0
    for ell, idx in sorted(byl.items()):
        W_ = np.array([rels[i] for i in idx]); n = len(idx)
        P = np.broadcast_to(np.eye(4, dtype=complex), (n, 4, 4)).copy()
        for p in range(ell): P = P @ Rall[W_[:, p]]
        D = P - target[idx][:, None, None]*np.eye(4)
        worst = max(worst, float(np.sqrt(np.real(np.einsum('nij,nij->n', np.conj(D), D))/4).max()))
    print(f"rescaled generators: max defect against (-1)^k over ALL relators {worst:.2e}", flush=True)
    json.dump({"seed": [[[float(z.real), float(z.imag)] for z in row] for Mx in R for row in Mx], "d": 4}, open("seed_theta_d4.json", "w"))
    ords = []
    for s in range(8):
        P = np.eye(4, dtype=complex); o = None
        for k in range(1, 65):
            P = P @ R[s]
            if np.allclose(P, P[0,0]*np.eye(4), atol=1e-8): o = k; break
        ords.append(o)
    print("orders of the generators modulo scalars:", ords, flush=True)
    print("wrote seed_theta_d4.json", flush=True)
