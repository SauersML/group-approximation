#!/usr/bin/env python3
"""v7: smoothed-maximum objective E = 2 + log(mean_r exp(beta (sq_r - 2)))/beta over the working set (argv[9] = beta), optional determinant pin, seed starts; p-power (near-max) objective, optional determinant pinning (kills the coboundary slide), large relator sets.
usage: optimize5.py pres.json modulus init d restarts iters n_unl seed p pin eps0 [stages]
  objective = mean_r sq_r^p over the working set (sq_r = normalized-HS squared defect of relator r);
  pin=1 keeps arg det U_s fixed at its initial value after every retraction; init as in v4 (seed:FILE etc.).
  Reports mean sq, max defect (unlifted / lifted) over the working set; saves the best tuple.
"""
import sys, json, time
import numpy as np
pres = json.load(open(sys.argv[1])); modulus = int(sys.argv[2]); init = sys.argv[3]
d = int(sys.argv[4]); restarts = int(sys.argv[5]); iters = int(sys.argv[6]); n_unl = int(sys.argv[7]); seed = int(sys.argv[8])
beta = float(sys.argv[9]); pw = beta; pin = int(sys.argv[10]); eps0 = float(sys.argv[11])
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
def forward(M, classes):
    """products and squared defects for every class; returns list of (PRE, SUF, D, sq)."""
    I = np.eye(d); out = []
    for ell, W, c in classes:
        n = W.shape[0]
        PRE = [np.broadcast_to(I, (n, d, d)).copy()]
        for p in range(ell): PRE.append(PRE[-1] @ M[W[:, p]])
        SUF = [np.broadcast_to(I, (n, d, d)).copy()]
        for q in range(ell): SUF.append(M[W[:, ell-1-q]] @ SUF[-1])
        D = PRE[ell] - c[:, None, None] * I
        sq = np.real(np.einsum('nij,nij->n', np.conj(D), D)) / d
        out.append((W, PRE, SUF, D, sq))
    return out
def backward(fw, G, wts):
    """accumulate G += sum_r wts_r * dsq_r/dU (conjugate-gradient convention, without the factor 2)."""
    for (W, PRE, SUF, D, sq), wt in zip(fw, wts):
        ell = W.shape[1]; Dw = D * (wt / d)[:, None, None]
        for p in range(ell):
            Lm = PRE[p]; Rm = SUF[ell-1-p]; letters = W[:, p]; direct = letters < 8
            if direct.any():
                Gam = np.conj(np.transpose(Lm[direct], (0,2,1))) @ Dw[direct] @ np.conj(np.transpose(Rm[direct], (0,2,1)))
                np.add.at(G, letters[direct], Gam)
            inv = ~direct
            if inv.any():
                Gam2 = Rm[inv] @ np.conj(np.transpose(Dw[inv], (0,2,1))) @ Lm[inv]
                np.add.at(G, letters[inv] - 8, Gam2)
def energy_and_grad(Us, CU):
    M = np.concatenate([Us, np.conj(np.transpose(Us, (0,2,1)))], axis=0)
    G = np.zeros((8, d, d), dtype=complex)
    fwu = forward(M, CU) if CU else []; fwl = forward(M, CL)
    sqs = [f[3+1] for f in fwu] + [f[4] for f in fwl]
    allsq = np.concatenate(sqs); ntot = allsq.size
    w = np.exp(beta * (allsq - 2.0)); Z = w.sum()
    E = 2.0 + np.log(Z / ntot) / beta
    ms = float(allsq.mean())
    mu = float(np.sqrt(np.concatenate([f[4] for f in fwu]).max())) if fwu else 0.0
    ml = float(np.sqrt(np.concatenate([f[4] for f in fwl]).max()))
    # dE/dsq_r = w_r / Z
    wts = []; k = 0
    for sq in sqs: wts.append(w[k:k+sq.size] / Z); k += sq.size
    backward(fwu + fwl, G, wts)
    return E, ms, mu, ml, 2.0 * G
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
            ph = np.angle(np.exp(1j * (np.angle(np.linalg.det(out[i])) - PIN[i])))   # reduced to (-pi, pi]
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
tag = f"best7_m{modulus}_{init.replace(':','_').replace('/','_')}_d{d}_p{pw}_pin{pin}_eps{eps0}_seed{seed}.npy"
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
    print(f"d={d} m={modulus} init={init} beta={beta} pin={pin} eps0={eps0} n_unl={len(z)} restart={rep}: Else={e:.4f} meansq={ms:.6f} maxdef_unl={mu:.4f} maxdef_lift={ml:.4f} t={time.time()-t0:.0f}s", flush=True)
    if best is None or e < best[0]:
        best = cur; np.save(tag, curU)
print(f"BEST d={d} m={modulus} init={init} beta={beta} pin={pin} eps0={eps0}: Else={best[0]:.4f} meansq={best[1]:.6f} maxdef_unl={best[2]:.4f} maxdef_lift={best[3]:.4f} saved={tag}", flush=True)
