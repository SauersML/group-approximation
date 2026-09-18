#!/usr/bin/env python3
"""Baselines at equal radius, floating point (scouting):
  (1) Dirichlet top eigenvalue of P on the Cayley ball B_r of F, r <= RC;
  (2) the moment bound from the Cayley return moments of length <= 2r
      (largest Ritz value of the Lanczos/Jacobi matrix built from c_0..c_r of P^2,
      i.e. the Hankel optimum the moment-optimum node computes exactly), using the
      EP-G table in ../thompson-f-cogrowth-2026-09-17/cogrowth_table.csv;
  (3) the same moment bound for the Schreier return moments (window_eig_R*.json).
Usage: compare_cayley.py RC RS"""
import sys, json, csv
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from mpmath import mp, mpf, matrix, eigsy
from cosets import IDENT, GENS, comp

mp.dps = 60


def moment_bound(M):
    """M[j] = <P^(2j) d, d>, j = 0..J. Largest zero of the orthogonal polynomial
    p_k for the measure of P^2 (k = floor((J+1)/2)), via Cholesky of the Hankel
    matrices; returns sqrt (a lower bound for ||P||)."""
    J = len(M) - 1
    k = (J + 1) // 2
    Hm = matrix(k, k)
    H1 = matrix(k, k)
    for i in range(k):
        for j in range(k):
            Hm[i, j] = M[i + j]
            H1[i, j] = M[i + j + 1] if i + j + 1 <= J else None
    # generalized eigenproblem H1 v = x Hm v  -> Cholesky
    L = mp.cholesky(Hm)
    Li = L ** -1
    C = Li * H1 * Li.T
    C = (C + C.T) / 2
    ev = eigsy(C, eigvals_only=True)
    return float(mp.sqrt(max(ev)))


def main():
    RC, RS = int(sys.argv[1]), int(sys.argv[2])
    rows = list(csv.DictReader(open("../thompson-f-cogrowth-2026-09-17/cogrowth_table.csv")))
    c = [int(r["c_n_trivial_words"]) for r in rows]
    cay_mom = {}
    for N in range(2, 32):
        M = [mpf(c[j]) / mpf(16) ** j for j in range(N + 1)]
        # need 2k-1 <= N moments of P^2: use M_0..M_(2k-1) with k = (N+1)//2
        if N % 2 == 0:
            M = M[:N]
        cay_mom[N] = moment_bound(M)
    # Cayley ball windows
    idx = {IDENT: 0}
    reps = [IDENT]
    dist = [0]
    nbr = []
    frontier = [0]
    for r in range(1, RC + 2):
        nf = []
        for v in frontier:
            row = []
            for t in GENS:
                h = comp(t, reps[v])
                w = idx.get(h)
                if w is None:
                    if r > RC:
                        row.append(-1)
                        continue
                    w = len(reps); idx[h] = w; reps.append(h); dist.append(r); nf.append(w)
                row.append(w)
            nbr.append(row)
        frontier = nf
    nbr = np.array(nbr); dist = np.array(dist)
    n = len(dist)
    rr = np.repeat(np.arange(n), 4); cc = nbr.reshape(-1); ok = cc >= 0
    A = sp.csr_matrix((np.full(ok.sum(), 0.25), (rr[ok], cc[ok])), shape=(n, n))
    cay_win = {}
    for r in range(2, RC + 1):
        m = int((dist <= r).sum())
        Ar = A[:m, :m]
        lam = float(np.linalg.eigvalsh(Ar.toarray())[-1]) if m < 400 else float(eigsh(Ar, k=1, which="LA", tol=1e-12)[0][0])
        cay_win[r] = (m, lam)
    sch = json.load(open(f"window_eig_R{RS}.json"))
    smom = sch["moments"]  # m_j = <P^j d_o, d_o>, j <= 2RS
    sch_mom = {}
    for N in range(2, RS + 1):
        M = [mpf(smom[2 * j]) for j in range(N + 1)]
        if N % 2 == 0:
            M = M[:N]
        sch_mom[N] = moment_bound(M)
    out = []
    print("r | cayley ball, lam | schreier ball, lam | cayley moments len<=2r | schreier moments len<=2r")
    for r in range(2, max(RC, RS) + 1):
        cw = cay_win.get(r); sw = sch["windows"].get(str(r))
        line = dict(r=r, cayley_ball=cw, schreier_ball=(sw["ball"], sw["dirichlet"]) if sw else None,
                    cayley_moment=cay_mom.get(r), schreier_moment=sch_mom.get(r))
        out.append(line)
        print(line, flush=True)
    json.dump(out, open("compare_cayley.json", "w"), indent=1)


if __name__ == "__main__":
    main()
