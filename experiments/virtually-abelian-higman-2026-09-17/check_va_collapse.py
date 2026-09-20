"""Sanity checks for virtually-abelian-higman-tuples-collapse-opnorm.

Not part of the proof.  Two checks.

1. Census distance certificates.  For each stored Z/4 census optimum P of
   higman-opnorm-collapse-is-a-one-unitary-z4-problem, form U_i = S^i P S^-i,
   recompute the Higman defect

       D(U) = max_i || U_i U_(i+1) U_i^* - U_(i+1)^2 ||_op

   and M(U) = max_i ||U_i - 1||_op, and print the certified lower bound

       dist(U, VA) >= min((1/2 - D)/5, (M - D)/6)                   (VA-dist)

   on the operator-norm distance from U to every tuple generating a
   virtually abelian subgroup of the same U(N).

2. Generic-phase monomial search.  Minimise D(u) - min(1/2, M(u)) over
   tuples u_i = diag(phases_i) * perm_i in U(n) with arbitrary real phases
   (so the generated group is virtually abelian but typically infinite),
   by random restarts plus coordinate descent on the phases and random
   transposition moves on the permutations.  The theorem predicts the
   minimum is >= 0.

Usage: python3 check_va_collapse.py [seed]
"""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CENSUS = os.path.join(HERE, "..", "higman-minimax-2026-09-17")


def op(A):
    return np.linalg.norm(A, 2)


def block_shift(N):
    # identical to equivariant_search.block_shift
    m = N // 4
    S = np.zeros((N, N))
    for j in range(4):
        S[j * m:(j + 1) * m, ((j + 1) % 4) * m:((j + 2) % 4) * m or N] = np.eye(m)
    return S


def defect(U):
    return max(op(U[i] @ U[(i + 1) % 4] @ U[i].conj().T
                  - U[(i + 1) % 4] @ U[(i + 1) % 4]) for i in range(4))


def maxdist(U):
    I = np.eye(U[0].shape[0])
    return max(op(u - I) for u in U)


def census():
    print("== census distance certificates (VA-dist) ==")
    for name in ["chain64.npy", "chain80.npy", "chain96.npy"]:
        path = os.path.join(CENSUS, name)
        if not os.path.exists(path):
            print(name, "missing")
            continue
        P = np.load(path)
        N = P.shape[0]
        S = block_shift(N)
        U = [np.linalg.matrix_power(S, i) @ P @ np.linalg.matrix_power(S.T, i)
             for i in range(4)]
        unit = max(op(u @ u.conj().T - np.eye(N)) for u in U)
        D, M = defect(U), maxdist(U)
        lb = min((0.5 - D) / 5, (M - D) / 6)
        print(f"{name:12s} N={N:3d} unitarity_err={unit:.1e} D={D:.6f} "
              f"M={M:.6f} dist_to_VA>={lb:.6f}")


def monomial(phases, perm):
    n = len(perm)
    A = np.zeros((n, n), dtype=complex)
    A[perm, np.arange(n)] = np.exp(1j * phases)
    return A


def score(ph, pm):
    U = [monomial(ph[i], pm[i]) for i in range(4)]
    D, M = defect(U), maxdist(U)
    return D - min(0.5, M), D, M


def search(rng, n, restarts=40, sweeps=30):
    best = (np.inf, None, None)
    for _ in range(restarts):
        ph = rng.uniform(0, 2 * np.pi, size=(4, n))
        pm = [rng.permutation(n) for _ in range(4)]
        s = score(ph, pm)
        for _ in range(sweeps):
            for i in range(4):
                for k in range(n):
                    for step in (0.3, -0.3, 0.05, -0.05):
                        ph2 = ph.copy()
                        ph2[i, k] += step
                        s2 = score(ph2, pm)
                        if s2[0] < s[0]:
                            ph, s = ph2, s2
                a, b = rng.choice(n, 2, replace=False)
                pm2 = [p.copy() for p in pm]
                pm2[i][[a, b]] = pm2[i][[b, a]]
                s2 = score(ph, pm2)
                if s2[0] < s[0]:
                    pm, s = pm2, s2
        if s[0] < best[0]:
            best = s
    return best


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    rng = np.random.default_rng(seed)
    census()
    print("== generic-phase monomial search: min of D - min(1/2, M) ==")
    for n in (2, 3, 4, 6, 8):
        m, D, M = search(rng, n)
        print(f"n={n:2d} min_margin={m:.6f} at D={D:.6f} M={M:.6f}")


if __name__ == "__main__":
    main()
