#!/usr/bin/env python3
"""v3: staged relator-length continuation + structured initialization.
usage: optimize3.py pres.json modulus init d restarts iters n_unl seed
init in {random, trivial, perm2, perm3}: trivial = U_s = exp(i eps H_s) near identity;
perm2 = permutation representation of Sp_4(Z) on (Z/2)^4 (d=16), perm3 = on (Z/3)^4 (d=81),
perturbed by exp(i eps H). Objective = mean_unlifted + w * mean_lifted (w = weight arg).
"""
import sys, json, time, itertools
import numpy as np
pres = json.load(open(sys.argv[1])); sector_arg = sys.argv[2]; init = sys.argv[3]
if sector_arg.startswith("file:"):
    PH = json.load(open(sector_arg[5:]))["phases"]; modulus = 2
else:
    PH = None; modulus = int(sector_arg)
d = int(sys.argv[4]); restarts = int(sys.argv[5]); iters = int(sys.argv[6]); n_unl = int(sys.argv[7]); seed = int(sys.argv[8])
wlift = float(sys.argv[9]) if len(sys.argv) > 9 else 1.0
eps0 = float(sys.argv[10]) if len(sys.argv) > 10 else 0.3
rng = np.random.default_rng(seed)
rels = [tuple(r) for r in pres["relators"]]; lifts = pres["lifts"] if PH is None else PH; GEN = [np.array(g) for g in pres["generators"]]
nz = [i for i, k in enumerate(lifts) if k % modulus != 0]
if PH is not None and len(nz) > n_unl: nz = list(rng.choice(nz, size=n_unl, replace=False))
z = [i for i, k in enumerate(lifts) if k % modulus == 0]
if len(z) > n_unl: z = list(rng.choice(z, size=n_unl, replace=False))
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
def part(M, classes, G, weight):
    I = np.eye(d); tot = 0.0; mx = 0.0; cnt = 0
    for ell, W, c in classes:
        n = W.shape[0]; cnt += n
        PRE = [np.broadcast_to(I, (n, d, d)).copy()]
        for p in range(ell): PRE.append(PRE[-1] @ M[W[:, p]])
        SUF = [np.broadcast_to(I, (n, d, d)).copy()]
        for q in range(ell): SUF.append(M[W[:, ell-1-q]] @ SUF[-1])
        D = PRE[ell] - c[:, None, None] * I
        sq = np.real(np.einsum('nij,nij->n', np.conj(D), D)) / d
        tot += sq.sum(); mx = max(mx, float(np.sqrt(sq.max())))
        for p in range(ell):
            Lm = PRE[p]; Rm = SUF[ell-1-p]; letters = W[:, p]; direct = letters < 8
            if direct.any():
                Gam = np.conj(np.transpose(Lm[direct], (0,2,1))) @ D[direct] @ np.conj(np.transpose(Rm[direct], (0,2,1)))
                np.add.at(G, letters[direct], (weight / cnt_total(classes)) * Gam)
            inv = ~direct
            if inv.any():
                Gam2 = Rm[inv] @ np.conj(np.transpose(D[inv], (0,2,1))) @ Lm[inv]
                np.add.at(G, letters[inv] - 8, (weight / cnt_total(classes)) * Gam2)
    return tot / cnt, mx
def cnt_total(classes): return sum(W.shape[0] for _, W, _ in classes)
def energy_and_grad(Us, CU):
    M = np.concatenate([Us, np.conj(np.transpose(Us, (0,2,1)))], axis=0)
    G = np.zeros((8, d, d), dtype=complex)
    eu, mu = part(M, CU, G, 1.0 / d) if CU else (0.0, 0.0)
    el, ml = part(M, CL, G, wlift / d)
    return eu + wlift * el, eu, el, mu, ml, 2.0 * G
def tangent(Us, grad):
    out = np.empty_like(grad)
    for i in range(8):
        H = Us[i].conj().T @ grad[i]; H = (H + H.conj().T) / 2; out[i] = grad[i] - Us[i] @ H
    return out
def retract(Us, V): return np.stack([polar(Us[i] + V[i]) for i in range(8)])
def descend(Us, CU, iters):
    e, eu, el, mu, ml, g = energy_and_grad(Us, CU); eta = 0.1; fails = 0
    for it in range(iters):
        gr = tangent(Us, g); cand = retract(Us, -eta * gr)
        e2, eu2, el2, mu2, ml2, g2 = energy_and_grad(cand, CU)
        if e2 < e: Us, e, eu, el, mu, ml, g = cand, e2, eu2, el2, mu2, ml2, g2; eta = min(eta*1.2, 3.0); fails = 0
        else:
            eta *= 0.5; fails += 1
            if eta < 1e-9 or fails > 40: break
    return Us, (e, eu, el, mu, ml)
def rand_herm():
    A = rng.standard_normal((d,d)) + 1j*rng.standard_normal((d,d)); A = (A + A.conj().T)/2
    return A / np.linalg.norm(A, 2)
def expiH(H):
    w, V = np.linalg.eigh(H); return (V * np.exp(1j*w)) @ V.conj().T
def perm_rep(p):
    pts = list(itertools.product(range(p), repeat=4)); idx = {v: i for i, v in enumerate(pts)}
    assert len(pts) == d
    Us = []
    for g in GEN:
        P = np.zeros((d, d), dtype=complex)
        for v in pts:
            w = tuple(int(x) % p for x in (g @ np.array(v)))
            P[idx[w], idx[v]] = 1
        Us.append(P)
    return np.stack(Us)
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
    base = np.stack([np.eye(d, dtype=complex)]*8) if init == "trivial" else perm_rep(2 if init == "perm2" else 3)
    return np.stack([base[i] @ expiH(eps * rand_herm()) for i in range(8)])
stages = [6, 8, 10, 12]
best = None
for rep in range(restarts):
    Us = initial(eps0 * (0.5 + rng.random()))
    t0 = time.time()
    for ml_ in stages:
        CU = classes_of(z, maxlen=ml_)
        Us, st = descend(Us, CU, iters)
    # basin hopping
    cur = st; curU = Us
    for hop in range(6):
        cand = np.stack([curU[i] @ expiH(0.15 * rand_herm()) for i in range(8)])
        candU, st2 = descend(cand, CU, iters)
        if st2[0] < cur[0]: cur, curU = st2, candU
    e, eu, el, mu, ml = cur
    print(f"d={d} m={sector_arg} init={init} w={wlift} eps0={eps0} restart={rep}: E={e:.6f} unlifted={eu:.6f} lifted={el:.6f} maxdef_unl={mu:.4f} maxdef_lift={ml:.4f} t={time.time()-t0:.0f}s", flush=True)
    if best is None or e < best[0]:
        best = cur
        tag = f"best_m{sector_arg.replace(':','_').replace('/','_')}_{init.replace(':','_').replace('/','_')}_d{d}_eps{eps0}_seed{seed}.npy"
        np.save(tag, curU)
print(f"BEST d={d} m={sector_arg} init={init} w={wlift} eps0={eps0}: E={best[0]:.6f} unlifted={best[1]:.6f} lifted={best[2]:.6f} maxdef_unl={best[3]:.4f} maxdef_lift={best[4]:.4f}", flush=True)
