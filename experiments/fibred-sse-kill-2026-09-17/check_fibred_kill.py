#!/usr/bin/env python3
"""Numerical replay of sticky-cylinder-gadget-compositions-cannot-prove-sseh.

Checks, on random weighted projection games B = (L, R, E) with left arity <= k
and uniform edge weights out of each left vertex:
  (a) Phi_P(X u N(X)) <= (k-1)/(k+1)                       (one-step walk on L u R)
  (b) 1 - Phi_{P^(2s)}(A) >= (1 - Phi_P(A))^(2s)            (Jensen, even powers)
  (c) 1 - Phi_{P_R^s}(X) >= k^-s, 1 - Phi_{P_L^s}(N(X)) >= k^-s   (squared walks)
  (d) the first-coordinate cylinder of X in the tensor square has the same
      volume and expansion as X                              (tensor fibration)
  (e) a gadget graph G' on R x {0,1}^m whose edges follow P_R and a noisy
      hypercube on the gadget coordinate: Phi_{G'}(pi^-1 X) = Phi_{P_R}(X)
  (f) scale sweep: growing X one vertex at a time, the volume of X u N(X)
      moves in increments <= varsigma = (k+1) max_x mu(x).
  (g) stickiness: every vertex of A = X u N(X) stays in A after t walk steps
      with probability >= k^-ceil(t/2) (odd t included), and the union cylinder
      {some coordinate in X} of two independent eps-noised copies of P_R is
      pointwise (1-eps)/k-sticky.
Exit code 0 iff every check passes. Usage: python3 check_fibred_kill.py [seed]
"""
import itertools
import sys

import numpy as np

TOL = 1e-10


def random_game(rng, nL, nR, k):
    """Return edge-weight matrix Wt (nL x nR): left vertex c has weight w_c spread
    uniformly over 1..k distinct right neighbours."""
    Wt = np.zeros((nL, nR))
    for c in range(nL):
        a = int(rng.integers(1, min(k, nR) + 1))
        nb = rng.choice(nR, size=a, replace=False)
        wc = rng.uniform(0.2, 3.0)
        Wt[c, nb] = wc / a
    return Wt  # right vertices without edges are dropped by the caller


def full_graph(Wt):
    nL, nR = Wt.shape
    n = nL + nR
    M = np.zeros((n, n))
    M[:nL, nL:] = Wt
    M[nL:, :nL] = Wt.T
    return M  # symmetric edge-weight matrix


def expansion(M, S):
    """Phi(S) for symmetric edge-weight matrix M: weight leaving S / volume of S."""
    vol = M.sum(axis=1)
    ind = np.zeros(M.shape[0])
    ind[list(S)] = 1.0
    volS = vol @ ind
    inside = ind @ M @ ind
    return (volS - inside) / volS, volS / vol.sum()


def walk_power_edges(M, t):
    """Edge-weight matrix of t steps of the walk from stationary measure."""
    vol = M.sum(axis=1)
    P = M / vol[:, None]
    return vol[:, None] * np.linalg.matrix_power(P, t)


def restricted_square(Wt, side):
    """Edge-weight matrix of the two-step walk restricted to one side."""
    volL = Wt.sum(axis=1)
    volR = Wt.sum(axis=0)
    if side == "R":
        return Wt.T @ np.diag(1.0 / volL) @ Wt
    return Wt @ np.diag(1.0 / volR) @ Wt.T


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 20260917
    rng = np.random.default_rng(seed)
    worst = {"a": -1, "b": -1, "c": -1, "d": 0, "e": 0, "f": -1}
    fails = 0
    for trial in range(60):
        k = int(rng.integers(2, 6))
        nL, nR = int(rng.integers(4, 12)), int(rng.integers(3, 9))
        Wt = random_game(rng, nL, nR, k)
        keepR = Wt.sum(axis=0) > 0
        Wt = Wt[:, keepR]
        nR = Wt.shape[1]
        M = full_graph(Wt)
        c = 2.0 / (k + 1)
        for _ in range(6):
            X = [x for x in range(nR) if rng.random() < 0.4] or [0]
            NX = sorted(set(np.nonzero(Wt[:, X].sum(axis=1))[0]))
            A = NX + [nL + x for x in X]
            phi, _ = expansion(M, A)
            worst["a"] = max(worst["a"], phi - (k - 1) / (k + 1))
            if phi > (k - 1) / (k + 1) + TOL:
                fails += 1
            for s in (1, 2, 3):
                phi2, _ = expansion(walk_power_edges(M, 2 * s), A)
                gap = (1 - phi) ** (2 * s) - (1 - phi2)
                worst["b"] = max(worst["b"], gap)
                if gap > TOL:
                    fails += 1
            MR, ML = restricted_square(Wt, "R"), restricted_square(Wt, "L")
            for s in (1, 2, 3):
                PR = walk_power_edges(MR, s)
                PL = walk_power_edges(ML, s)
                pR, _ = expansion(PR, X)
                pL, _ = expansion(PL, NX)
                gap = max(k ** -s - (1 - pR), k ** -s - (1 - pL))
                worst["c"] = max(worst["c"], gap)
                if gap > TOL:
                    fails += 1
        # (d) tensor square: product walk on (L u R)^2 restricted to L^2 u R^2
        if nL * nR <= 60:
            T = np.block([[np.zeros((nL * nL, nL * nL)), np.kron(Wt, Wt) / Wt.sum()],
                          [np.kron(Wt, Wt).T / Wt.sum(), np.zeros((nR * nR, nR * nR))]])
            X = [0]
            NX = sorted(set(np.nonzero(Wt[:, X].sum(axis=1))[0]))
            A = NX + [nL + x for x in X]
            phi, mu = expansion(M, A)
            cyl = [a * nL + b for a in NX for b in range(nL)] + \
                  [nL * nL + a * nR + b for a in X for b in range(nR)]
            phiT, muT = expansion(T, cyl)
            d = max(abs(phi - phiT), abs(mu - muT))
            worst["d"] = max(worst["d"], d)
            if d > 1e-9:
                fails += 1
        # (e) gadget graph over P_R with noisy hypercube coordinate
        m, rho = 3, 0.7
        MR = restricted_square(Wt, "R")
        cube = np.zeros((2 ** m, 2 ** m))
        for z, w in itertools.product(range(2 ** m), repeat=2):
            dist = bin(z ^ w).count("1")
            cube[z, w] = ((1 + rho) / 2) ** (m - dist) * ((1 - rho) / 2) ** dist
        G = np.kron(MR, cube)
        X = [x for x in range(nR) if rng.random() < 0.5] or [0]
        pre = [x * 2 ** m + z for x in X for z in range(2 ** m)]
        e1 = expansion(G, pre)
        e0 = expansion(MR, X)
        d = max(abs(e1[0] - e0[0]), abs(e1[1] - e0[1]))
        worst["e"] = max(worst["e"], d)
        if d > 1e-9:
            fails += 1
        # (g) stickiness: pointwise return bounds, odd powers, union cylinders
        vol = M.sum(axis=1)
        P = M / vol[:, None]
        X = [x for x in range(nR) if rng.random() < 0.4] or [0]
        NX = sorted(set(np.nonzero(Wt[:, X].sum(axis=1))[0]))
        A = NX + [nL + x for x in X]
        for t in (1, 2, 3, 4, 5):
            Pt = np.linalg.matrix_power(P, t)
            stick = Pt[np.ix_(A, A)].sum(axis=1).min()
            gap = k ** -((t + 1) // 2) - stick
            worst["g"] = max(worst.get("g", -1), gap)
            if gap > TOL:
                fails += 1
        MR = restricted_square(Wt, "R")
        PR = MR / MR.sum(axis=1)[:, None]
        eps = rng.uniform(0, 0.5)
        PRn = (1 - eps) * PR + eps * (MR.sum(axis=1) / MR.sum())[None, :]
        prod = np.kron(PRn, PRn)  # two coordinates moving independently
        U = [a * nR + b for a in range(nR) for b in range(nR) if a in X or b in X]
        stick = prod[np.ix_(U, U)].sum(axis=1).min()
        gap = (1 - eps) / k - stick
        worst["g"] = max(worst.get("g", -1), gap)
        if gap > TOL:
            fails += 1
        # (f) scale sweep increments
        vol = M.sum(axis=1)
        mu = vol / vol.sum()
        vs = (k + 1) * mu[nL:].max()
        prev, X = 0.0, []
        for x in rng.permutation(nR):
            X.append(int(x))
            NX = sorted(set(np.nonzero(Wt[:, X].sum(axis=1))[0]))
            _, cur = expansion(M, NX + [nL + y for y in X])
            worst["f"] = max(worst["f"], (cur - prev) - vs)
            if cur - prev > vs + TOL:
                fails += 1
            prev = cur
    print("seed", seed)
    print("max violation (a) Phi - (k-1)/(k+1):", worst["a"])
    print("max violation (b) Jensen gap:", worst["b"])
    print("max violation (c) k^-s - (1-Phi):", worst["c"])
    print("max |diff| (d) tensor cylinder:", worst["d"])
    print("max |diff| (e) gadget fibration:", worst["e"])
    print("max violation (f) increment - varsigma:", worst["f"])
    print("max violation (g) pointwise stickiness:", worst["g"])
    print("FAILS", fails)
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
