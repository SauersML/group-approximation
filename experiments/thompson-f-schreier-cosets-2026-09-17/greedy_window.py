#!/usr/bin/env python3
"""Scouting: greedy Perron growth of window sets inside a computed Schreier ball.
Start from B_r0; repeatedly add the fraction `frac` of outer-boundary vertices (inside
the stored ball B_R) with largest score sum_{w in S, w ~ x} psi(w), where psi is the
current Dirichlet Perron vector.  Compares lambda(S) with lambda(ball of equal size).
Usage: greedy_window.py R r0 budget frac"""
import sys, json
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh


def main():
    R, r0, budget, frac = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    nbr = np.load(f"nbr_R{R}.npy"); dist = np.load(f"dist_R{R}.npy")
    n = len(dist)
    rows = np.repeat(np.arange(n), 4); cols = nbr.reshape(-1); ok = cols >= 0
    A = sp.csr_matrix((np.full(ok.sum(), 0.25), (rows[ok], cols[ok])), shape=(n, n))
    inS = dist <= r0
    hist = []
    v0 = None
    while True:
        S = np.nonzero(inS)[0]
        As = A[S][:, S]
        lam, vec = eigsh(As, k=1, which="LA", tol=1e-10, v0=v0)
        psi = np.abs(vec[:, 0]); lam = float(lam[0])
        hist.append((len(S), lam, int(dist[S].max())))
        print(len(S), f"{lam:.6f}", "maxdist", int(dist[S].max()), flush=True)
        if len(S) >= budget:
            break
        full = np.zeros(n); full[S] = psi
        score = A @ full
        score[inS] = -1
        cand = np.nonzero(score > 0)[0]
        if len(cand) == 0:
            break
        k = max(1, int(frac * len(cand)))
        k = min(k, budget - len(S)) if budget > len(S) else k
        top = cand[np.argsort(-score[cand])[:k]]
        inS[top] = True
        v0 = None
    json.dump(dict(R=R, r0=r0, frac=frac, history=hist), open(f"greedy_R{R}_r{r0}_f{frac}.json", "w"), indent=1)


if __name__ == "__main__":
    main()
