"""Basin test for the planted S_5 calibration of the Thompson V normalized-HS probe.

Run on MSI only.  The planted relator set of calibrate_hs.py (Bleak--Quick words raised to
their orders in S_5) has an exact balanced-spectrum solution: the 6-dimensional irreducible
representation rho = Lambda^2(standard) of S_5, and its direct sums at d = 6k.  This script

  1. builds rho exactly and checks that the planted relators vanish on it (sanity);
  2. writes rho(x), rho(y) in the probe's parametrization u = W_u D6 W_u^*, v = W_v D3 W_v^*;
  3. starts descent from W_exact * exp(eps * random skew-Hermitian) for a range of eps and
     reports the fraction of runs that return to defect ~0.

So it measures how wide the basin of an exact far-from-trivial solution is under the same
optimizer.  If Haar starts never succeed but small eps does, the probe's plateaus from
random starts carry no information about the existence of models.

Usage: python3 basin_hs.py --d 6 12 --eps 0.01 0.1 0.3 1 3 --trials 5 --iters 1500 --out FILE.json
"""
import argparse
import json
import os
import sys
import time

import numpy as np
from scipy.linalg import expm, schur

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import calibrate_hs as C


def planted_generators(seed):
    """Same random choice as calibrate_hs.planted_s5_relators(seed), returning x, y too."""
    rng = np.random.default_rng(1000 + seed)
    while True:
        a = rng.permutation(5)
        b = rng.permutation(5)
        x = np.arange(5)
        x[a[0]], x[a[1]] = a[1], a[0]
        x[a[2]], x[a[3]], x[a[4]] = a[3], a[4], a[2]
        y = np.arange(5)
        y[b[0]], y[b[1]], y[b[2]] = b[1], b[2], b[0]
        if C.group_order([tuple(x), tuple(y)]) == 120:
            return x, y


def lambda2_standard(p):
    P = C.perm_matrix(p).astype(float)
    ones = np.ones((5, 1)) / np.sqrt(5)
    q, _ = np.linalg.qr(np.hstack([ones, np.eye(5)[:, :4]]))
    B = q[:, 1:5]
    S = B.T @ P @ B
    pairs = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    R = np.zeros((6, 6))
    for a_, (i, j) in enumerate(pairs):
        for b_, (k, l) in enumerate(pairs):
            R[a_, b_] = S[i, k] * S[j, l] - S[i, l] * S[j, k]
    return R


def parametrize(Umat, k, d):
    """Return unitary W with W diag(roots_diag(d, k)) W^* = Umat (Umat unitary, balanced spectrum)."""
    T, Z = schur(Umat.astype(complex), output="complex")
    ev = np.diag(T)
    target = C.roots_diag(d, k)
    cols = [[] for _ in range(k)]
    for c in range(d):
        r = int(np.round(np.angle(ev[c]) / (2 * np.pi / k))) % k
        cols[r].append(c)
    order = []
    counters = [0] * k
    for pos in range(d):
        r = pos % k
        order.append(cols[r][counters[r]])
        counters[r] += 1
    W = Z[:, order]
    assert np.allclose((W * target) @ W.conj().T, Umat, atol=1e-8), "parametrization failed"
    return W


def descend(W, D, rels, d, iters, lr0):
    def build(W):
        return {x: (W[x] * D[x]) @ W[x].conj().T for x in "uv"}

    U = build(W)
    L, defs, G = C.loss_and_grads(U, d, rels)
    lr, it = lr0, 0
    for it in range(iters):
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
    return L, float(np.sqrt(max(defs))), it + 1


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--d", type=int, nargs="+", default=[6, 12])
    ap.add_argument("--eps", type=float, nargs="+", default=[0.01, 0.1, 0.3, 1.0, 3.0])
    ap.add_argument("--trials", type=int, default=5)
    ap.add_argument("--iters", type=int, default=1500)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--lr", type=float, default=0.5)
    ap.add_argument("--out", default="basin_hs_results.json")
    a = ap.parse_args()
    rels, ms = C.planted_s5_relators(a.seed)
    x, y = planted_generators(a.seed)
    rx, ry = lambda2_standard(x), lambda2_standard(y)
    results = {"planted_powers": ms, "runs": []}
    for d in a.d:
        k = d // 6
        Ux, Uy = np.kron(np.eye(k), rx), np.kron(np.eye(k), ry)
        D = {"u": C.roots_diag(d, 6), "v": C.roots_diag(d, 3)}
        Wex = {"u": parametrize(Ux, 6, d), "v": parametrize(Uy, 3, d)}
        L0, _, _ = C.loss_and_grads({"u": Ux.astype(complex), "v": Uy.astype(complex)}, d, rels)
        print(json.dumps({"d": d, "exact_solution_mean_sq_defect": L0}), flush=True)
        rng = np.random.default_rng(7 + d)
        for eps in a.eps:
            for t in range(a.trials):
                W0 = {}
                for s in "uv":
                    A = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
                    A = (A - A.conj().T) / 2
                    A /= np.linalg.norm(A, 2)
                    W0[s] = Wex[s] @ expm(eps * A)
                t0 = time.time()
                L, mx, its = descend(W0, D, rels, d, a.iters, a.lr)
                row = {"d": d, "eps": eps, "trial": t, "final_mean_sq_defect": L,
                       "final_max_hs_defect": mx, "iters_done": its, "seconds": time.time() - t0}
                results["runs"].append(row)
                print(json.dumps(row), flush=True)
                json.dump(results, open(a.out, "w"), indent=1)
