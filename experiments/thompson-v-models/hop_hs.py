"""Basin-hopping search for normalized-HS models, calibrated on the planted S_5 set.

Run on MSI only.  Same parametrization and loss as calibrate_hs.py.  After an initial descent
from a Haar start, each hop multiplies the current best W_u, W_v by exp(eps * random
skew-Hermitian of operator norm 1), descends again, and keeps the result if the mean squared
defect improved.  The basin test (basin_hs.py) motivates eps: planted exact solutions attract
descent from eps <= 0.3 but not from eps = 3.

A relator set counts as SOLVED at dimension d when some run reaches max relator HS defect
below --tol.  The point is the comparison: if hopping solves the planted set from Haar starts
and still plateaus on the V set, the V plateau is evidence (not proof) against small-d models;
if hopping fails on the planted set too, no plateau of this probe says anything about V.

Usage: python3 hop_hs.py --sets planted V --dims 6 12 24 --seeds 3 --hops 40 --eps 0.7 --out FILE.json
"""
import argparse
import itertools
import json
import os
import sys
import time

import numpy as np
from scipy.linalg import expm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import calibrate_hs as C


def descend(W, D, rels, d, iters, lr0):
    def build(W):
        return {x: (W[x] * D[x]) @ W[x].conj().T for x in "uv"}

    U = build(W)
    L, defs, G = C.loss_and_grads(U, d, rels)
    lr = lr0
    for _ in range(iters):
        newW = {}
        for x in "uv":
            H = W[x].conj().T @ G[x] @ W[x]
            M = D[x][:, None] * H.conj().T - H.conj().T * D[x][None, :]
            Ms = M.conj().T
            newW[x] = W[x] @ expm(lr * (-(Ms - Ms.conj().T) / 2))
        newU = build(newW)
        nL, ndefs, nG = C.loss_and_grads(newU, d, rels)
        if nL < L:
            W, U, L, defs, G = newW, newU, nL, ndefs, nG
            lr = min(lr * 1.2, 50.0)
        else:
            lr *= 0.5
            if lr < 1e-9:
                break
        if L < 1e-10:
            break
    return W, L, float(np.sqrt(max(defs)))


def perturb(W, eps, rng, d):
    out = {}
    for x in "uv":
        A = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
        A = (A - A.conj().T) / 2
        A /= np.linalg.norm(A, 2)
        out[x] = W[x] @ expm(eps * A)
    return out


def hop(d, seed, rels, hops, eps, iters0, iters_hop, lr, tol):
    rng = np.random.default_rng(seed)
    D = {"u": C.roots_diag(d, 6), "v": C.roots_diag(d, 3)}
    W = {"u": C.haar(d, rng), "v": C.haar(d, rng)}
    t0 = time.time()
    W, L, mx = descend(W, D, rels, d, iters0, lr)
    trace = [(0, L, mx)]
    best = (W, L, mx)
    for h in range(1, hops + 1):
        if best[2] < tol:
            break
        W2, L2, mx2 = descend(perturb(best[0], eps, rng, d), D, rels, d, iters_hop, lr)
        if L2 < best[1]:
            best = (W2, L2, mx2)
        trace.append((h, best[1], best[2]))
    return {"d": d, "seed": seed, "final_mean_sq_defect": best[1], "final_max_hs_defect": best[2],
            "solved": best[2] < tol, "hops_done": trace[-1][0], "trace": trace,
            "seconds": time.time() - t0}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--sets", nargs="+", default=["planted", "V"])
    ap.add_argument("--dims", type=int, nargs="+", default=[6, 12, 24])
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--hops", type=int, default=40)
    ap.add_argument("--eps", type=float, default=0.7)
    ap.add_argument("--iters0", type=int, default=1500)
    ap.add_argument("--iters-hop", type=int, default=400)
    ap.add_argument("--lr", type=float, default=0.5)
    ap.add_argument("--tol", type=float, default=0.05)
    ap.add_argument("--out", default="hop_hs_results.json")
    a = ap.parse_args()
    results = []
    for name, d, s in itertools.product(a.sets, a.dims, range(a.seeds)):
        if name == "V":
            rels = C.V_RELATORS
        elif name == "planted":
            rels, _ = C.planted_s5_relators(s)
        elif name == "null":
            rels = C.null_relators(s)
        else:
            raise ValueError(name)
        r = hop(d, s, rels, a.hops, a.eps, a.iters0, a.iters_hop, a.lr, a.tol)
        r["set"] = name
        results.append(r)
        print(json.dumps({k: r[k] for k in ("set", "d", "seed", "final_mean_sq_defect",
                                            "final_max_hs_defect", "solved", "hops_done", "seconds")}),
              flush=True)
        json.dump(results, open(a.out, "w"), indent=1)
