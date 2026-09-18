"""How far below beta = 1/4 does the l^infinity obstruction actually reach?

`brin-thompson-nv-max-type-size-functions-are-not-cnd` proves its item 2 for every
regularly varying index beta >= 1/4, and states explicitly that 0 < beta < 1/4 is not
claimed ("Grids up to {-7..7}^3 show no failure at beta = 0.1").  Misiewicz's theorem
(positive definite functions of ||x||_inf on R^3 are constant) would give all beta > 0
but is not imported.

Step 4 of the route (Schoenberg: cnd is preserved by K -> K^alpha, 0 < alpha < 1)
means a single certificate at index beta_0 kills every beta >= beta_0.  So the only
question is how small beta_0 can be made by a finite grid.  This script pushes the
grid size and reports, for each beta, the largest eigenvalue of the l^inf^beta kernel
restricted to the zero-sum subspace; a positive value at beta_0 lowers the claim's
threshold to beta_0.

Usage: python3 audit_beta_range.py [--kmax 7] [--betas 0.25,0.2,0.15,0.125]
"""
import argparse
import itertools

import numpy as np


def dist_matrix(k):
    P = np.array(list(itertools.product(range(-k, k + 1), repeat=3)), dtype=np.int16)
    return np.abs(P[:, None, :] - P[None, :, :]).max(-1)


def top_zero_sum_from_classes(D, beta):
    """Largest eigenvalue of P K P, P the projection onto zero-sum vectors."""
    K = D.astype(np.float64) ** beta
    n = K.shape[0]
    rs = K.sum(1) / n
    tot = rs.sum() / n
    M = K - rs[:, None] - rs[None, :] + tot
    M = (M + M.T) / 2
    return np.linalg.eigvalsh(M)[-1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=7)
    ap.add_argument("--betas", type=str, default="0.25,0.2,0.175,0.15,0.125,0.1")
    a = ap.parse_args()
    betas = [float(x) for x in a.betas.split(",")]
    print("largest eigenvalue on the zero-sum subspace of ||x-y||_inf^beta over {-k..k}^3")
    print("(positive => not cnd at that beta, hence, by Step 4 of the route, not cnd for"
          " every larger beta)")
    header = "  k  pts   " + "".join(f"beta={b:<8g}" for b in betas)
    print(header)
    for k in range(1, a.kmax + 1):
        D = dist_matrix(k)
        vals = [top_zero_sum_from_classes(D, b) for b in betas]
        print(f"  {k:<2d} {D.shape[0]:<5d} " + "".join(f"{v:+13.3e}" for v in vals), flush=True)


if __name__ == "__main__":
    main()
