#!/usr/bin/env python3
"""Top Dirichlet eigenvalue of P on Schreier balls B_r, r <= R, from nbr_R*.npy.
Also the Krylov/moment bound: moments m_j = <P^j d_o, d_o> for j <= 2r from the
same graph, and the largest Ritz value of the (r+1)-dim Krylov space.
Floating point (scouting); certify_window.py gives the rational certificate."""
import sys, json
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh


def main():
    R = int(sys.argv[1])
    nbr = np.load(f"nbr_R{R}.npy")
    dist = np.load(f"dist_R{R}.npy")
    n = len(dist)
    rows = np.repeat(np.arange(n), 4)
    cols = nbr.reshape(-1)
    ok = cols >= 0
    A = sp.csr_matrix((np.full(ok.sum(), 0.25), (rows[ok], cols[ok])), shape=(n, n))
    assert abs(A - A.T).max() < 1e-12
    out = {}
    for r in range(2, R + 1):
        m = int((dist <= r).sum())
        Ar = A[:m, :m]
        if m < 400:
            lam = float(np.linalg.eigvalsh(Ar.toarray())[-1])
        else:
            lam = float(eigsh(Ar, k=1, which="LA", tol=1e-12)[0][0])
        # Krylov moments from delta_o inside the full ball (exact for j <= 2R+1)
        out[r] = dict(ball=m, dirichlet=lam)
        print(r, m, f"{lam:.6f}", flush=True)
    # moments of the Schreier return walk: m_j for j <= 2R (vector stays in B_R for j <= R)
    v = np.zeros(n); v[0] = 1.0
    vs = [v]
    for j in range(R):
        vs.append(A @ vs[-1])
    mom = [float(vs[a] @ vs[b]) for a, b in [(j // 2, j - j // 2) for j in range(2 * R + 1)]]
    json.dump(dict(R=R, windows=out, moments=mom), open(f"window_eig_R{R}.json", "w"), indent=1)


if __name__ == "__main__":
    main()
