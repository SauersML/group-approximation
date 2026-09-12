#!/usr/bin/env python3
"""v5: p-power (near-max) objective, optional determinant pinning (kills the coboundary slide), large relator sets.
usage: optimize5.py pres.json modulus init d restarts iters n_unl seed p pin eps0 [stages]
  objective = mean_r sq_r^p over the working set (sq_r = normalized-HS squared defect of relator r);
  pin=1 keeps arg det U_s fixed at its initial value after every retraction; init as in v4 (seed:FILE etc.).
  Reports mean sq, max defect (unlifted / lifted) over the working set; saves the best tuple.
"""
import sys, json, time
import numpy as np
pres = json.load(open(sys.argv[1])); modulus = int(sys.argv[2]); init = sys.argv[3]
d = int(sys.argv[4]); restarts = int(sys.argv[5]); iters = int(sys.argv[6]); n_unl = int(sys.argv[7]); seed = int(sys.argv[8])
pw = float(sys.argv[9]); pin = int(sys.argv[10]); eps0 = float(sys.argv[11])
stages = [int(x) for x in sys.argv[12].split(",")] if len(sys.argv) > 12 else [8, 10, 12, 13]
rng = np.random.default_rng(seed)
rels = [tuple(r) for r in pres["relators"]]; lifts = pres["lifts"]
nz = [i for i, k in enumerate(lifts) if k % modulus != 0]
z = [i for i, k in enumerate(lifts) if k % modulus == 0]
if n_unl < len(z): z = list(rng.choice(z, size=n_unl, replace=False))
def classes_of(idx, maxlen=None):
    byl = {}
    for i in idx:
        if maxlen is None or len(rels[i]) <= maxlen: byl.setdefault(len(rels[i]), []).append(i)
    out = []
    for ell, ii in sorted(byl.items()):
        W = np.array([rels[i] for i in ii], dtype=np.int64); K = np.array([lifts[i] for i in ii], dtype=np.int64)
        out.append((ell, W, np.exp(2j*np.pi*(K % modulus)/modulus)))
    return out
CL = classes_of(nz)
def polar(X):
    U, _, Vh = np.linalg.svd(X); return U @ Vh
def part(M, classes, G, ntot):
    I = np.eye(d); tot = 0.0; mx = 0.0; sqsum = 0.0
    for ell, W, c in classes:
        n = W.shape[0]
        PRE = [np.broadcast_to(I, (n, d, d)).copy()]
        for p in range(ell): PRE.append(PRE[-1] @ M[W[:, p]])
        SUF = [np.broadcast_to(I, (n, d, d)).copy()]
        for q in range(ell): SUF.append(M[W[:, ell-1-q]] @ SUF[-1])
        D = PRE[ell] - c[:, None, None] * I
        sq = np.real(np.einsum('nij,nij->n', np.conj(D), D)) / d
        tot += (sq**pw).sum(); sqsum += sq.sum(); mx = max(mx, float(np.sqrt(sq.max())))
        wgt = (pw * sq**(pw-1) / (d * ntot))[:, None, None]     # d/dsq of sq^p, with sq = |D|^2/d
        Dw = D * wgt
        for p in range(ell):
            Lm = PRE[p]; Rm = SUF[ell-1-p]; letters = W[:, p]; direct = letters < 8
            if direct.any():
                Gam = np.conj(np.transpose(Lm[direct], (0,2,1))) @ Dw[direct] @ np.conj(np.transpose(Rm[direct], (0,2,1)))
                np.add.at(G, letters[direct], Gam)
            inv = ~direct
            if inv.any():
                Gam2 = Rm[inv] @ np.conj(np.transpose(Dw[inv], (0,2,1))) @ Lm[inv]
                np.add.at(G, letters[inv] - 8, Gam2)
    return tot, sqsum, mx
def energy_and_grad(Us, CU):
    M = np.concatenate([Us, np.conj(np.transpose(Us, (0,2,1)))], axis=0)
    G = np.zeros((8, d, d), dtype=complex)
    ntot = sum(W.shape[0] for _, W, _ in CU) + sum(W.shape[0] for _, W, _ in CL)
    tu, su, mu = part(M, CU, G, ntot) if CU else (0.0, 0.0, 0.0)
    tl, sl, ml = part(M, CL, G, ntot)
    return (tu + tl) / ntot, (su + sl) / ntot, mu, ml, 2.0 * G
def tangent(Us, grad):
    out = np.empty_like(grad)
    for i in range(8):
        H = Us[i].conj().T @ grad[i]; H = (H + H.conj().T) / 2; out[i] = grad[i] - Us[i] @ H
    return out
PIN = None
def retract(Us, V):
    out = np.stack([polar(Us[i] + V[i]) for i in range(8)])
    if pin and PIN is not None:
        for i in range(8):
            ph = np.angle(np.linalg.det(out[i])) - PIN[i]
            out[i] = out[i] * np.exp(-1j * ph / d)
    return out
def descend(Us, CU, iters):
    e, ms, mu, ml, g = energy_and_grad(Us, CU); eta = 0.1; fails = 0
    for it in range(iters):
        gr = tangent(Us, g); cand = retract(Us, -eta * gr)
        e2, ms2, mu2, ml2, g2 = energy_and_grad(cand, CU)
        if e2 < e: Us, e, ms, mu, ml, g = cand, e2, ms2, mu2, ml2, g2; eta = min(eta*1.2, 3.0); fails = 0
        else:
            eta *= 0.5; fails += 1
            if eta < 1e-9 or fails > 40: break
    return Us, (e, ms, mu, ml)
def rand_herm():
    A = rng.standard_normal((d,d)) + 1j*rng.standard_normal((d,d)); A = (A + A.conj().T)/2
    return A / np.linalg.norm(A, 2)
def expiH(H):
    w, V = np.linalg.eigh(H); return (V * np.exp(1j*w)) @ V.conj().T
def load_seed(fn):
    J = json.load(open(fn)); dd = J["d"]; arr = np.array(J["seed"], dtype=float)
    U = arr[:, :, 0] + 1j*arr[:, :, 1]
    return U.reshape(8, dd, dd)
def initial(eps):
    if init.startswith("seed:"):
        base = load_seed(init[5:]); assert base.shape[1] == d
        return np.stack([base[i] @ expiH(eps * rand_herm()) for i in range(8)])
    if init == "random":
        return np.stack([polar(rng.standard_normal((d,d)) + 1j*rng.standard_normal((d,d))) for _ in range(8)])
    base = np.stack([np.eye(d, dtype=complex)]*8)
    return np.stack([base[i] @ expiH(eps * rand_herm()) for i in range(8)])
best = None
tag = f"best5_m{modulus}_{init.replace(':','_').replace('/','_')}_d{d}_p{pw}_pin{pin}_eps{eps0}_seed{seed}.npy"
for rep in range(restarts):
    Us = initial(eps0)
    if init.startswith("seed:"):
        base = load_seed(init[5:]); PIN = [float(np.angle(np.linalg.det(base[i]))) for i in range(8)]
    else:
        PIN = [float(np.angle(np.linalg.det(Us[i]))) for i in range(8)]
    Us = retract(Us, np.zeros_like(Us))
    t0 = time.time()
    for ml_ in stages:
        CU = classes_of(z, maxlen=ml_)
        Us, st = descend(Us, CU, iters)
    cur = st; curU = Us
    for hop in range(3):
        cand = retract(np.stack([curU[i] @ expiH(0.1 * rand_herm()) for i in range(8)]), np.zeros_like(curU))
        candU, st2 = descend(cand, CU, iters)
        if st2[0] < cur[0]: cur, curU = st2, candU
    e, ms, mu, ml = cur
    print(f"d={d} m={modulus} init={init} p={pw} pin={pin} eps0={eps0} n_unl={len(z)} restart={rep}: Ep={e:.3e} meansq={ms:.6f} maxdef_unl={mu:.4f} maxdef_lift={ml:.4f} t={time.time()-t0:.0f}s", flush=True)
    if best is None or e < best[0]:
        best = cur; np.save(tag, curU)
print(f"BEST d={d} m={modulus} init={init} p={pw} pin={pin} eps0={eps0}: Ep={best[0]:.3e} meansq={best[1]:.6f} maxdef_unl={best[2]:.4f} maxdef_lift={best[3]:.4f} saved={tag}", flush=True)
