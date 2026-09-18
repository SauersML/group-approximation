#!/usr/bin/env python3
"""Numerical check of the power-uniform correction estimate (PU1).

Claim `bs12-conjugator-correction-is-power-uniform-defect`: for unitaries A,B
with finite-order B put

    Delta(A,B) = max_k || A B^k A^* - B^(2k) ||_op.

If Delta < 1 then X = (1/o) sum_k B^(2k) A B^(-k) satisfies B^2 X = X B, its
polar part C is unitary with C B C^* = B^2, and ||C - A|| <= 2 Delta.
Conversely every exact C has ||C - A|| >= Delta/2.

The script builds random exact packets (C0, B) in normal form, perturbs the
conjugator, and checks every inequality.  It also exhibits the gap between the
k=1 defect and Delta on a fine clock.

Usage: python3 verify_power_uniform_averaging.py [trials] [seed]
"""
import sys
import numpy as np
from scipy.linalg import expm, polar


def op(M):
    return np.linalg.norm(M, 2)


def orbit(a, o):
    """Doubling orbit of a mod o, listed a, a/2, a/4, ... (halving order)."""
    inv2 = pow(2, -1, o)
    out, x = [], a % o
    while True:
        out.append(x)
        x = (x * inv2) % o
        if x == out[0]:
            return out


def random_packet(rng, o, mult, ker_dim):
    """Exact packet C B C^* = B^2 with B of odd order o in normal form.

    Spectrum of B: every nonzero residue mod o with multiplicity `mult`
    (constant on doubling orbits), plus eigenvalue 1 with multiplicity ker_dim.
    C maps E_lambda to E_sqrt(lambda) as a shift with random wrap monodromy,
    and is a random unitary on ker(B-1).
    """
    seen, orbits = set(), []
    for a in range(1, o):
        if a not in seen:
            orb = orbit(a, o)
            seen.update(orb)
            orbits.append(orb)
    labels = []
    for orb in orbits:
        for x in orb:
            labels.append(x)
    n = len(labels) * mult + ker_dim
    B = np.zeros((n, n), complex)
    C = np.zeros((n, n), complex)
    pos = 0
    for orb in orbits:
        l = len(orb)
        W = np.linalg.qr(rng.normal(size=(mult, mult)) + 1j * rng.normal(size=(mult, mult)))[0]
        for p, x in enumerate(orb):
            sl = slice(pos + p * mult, pos + (p + 1) * mult)
            B[sl, sl] = np.exp(2j * np.pi * x / o) * np.eye(mult)
            # C sends block p (eigenvalue x) to block p+1 (eigenvalue x/2)
            q = (p + 1) % l
            tl = slice(pos + q * mult, pos + (q + 1) * mult)
            C[tl, sl] = W if q == 0 else np.eye(mult)
        pos += l * mult
    if ker_dim:
        sl = slice(pos, pos + ker_dim)
        B[sl, sl] = np.eye(ker_dim)
        C[sl, sl] = np.linalg.qr(rng.normal(size=(ker_dim, ker_dim))
                                 + 1j * rng.normal(size=(ker_dim, ker_dim)))[0]
    V = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))[0]
    return V @ C @ V.conj().T, V @ B @ V.conj().T


def delta_inf(A, B, o):
    Bk = np.eye(len(B), dtype=complex)
    worst = 0.0
    for _ in range(o):
        worst = max(worst, op(A @ Bk @ A.conj().T - Bk @ Bk))
        Bk = Bk @ B
    return worst


def average(A, B, o):
    X = np.zeros_like(A)
    Bk = np.eye(len(B), dtype=complex)
    Binv = B.conj().T
    Bmk = np.eye(len(B), dtype=complex)
    for _ in range(o):
        X += Bk @ Bk @ A @ Bmk
        Bk = Bk @ B
        Bmk = Bmk @ Binv
    return X / o


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    worst_ratio = 0.0
    for t in range(trials):
        o = int(rng.choice([3, 5, 7, 9, 15, 21, 31]))
        C0, B = random_packet(rng, o, int(rng.integers(1, 3)), int(rng.integers(0, 3)))
        n = len(B)
        H = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
        H = (H + H.conj().T) / 2
        H /= op(H)
        A = C0 @ expm(1j * rng.uniform(0.01, 0.2) * H)
        D = delta_inf(A, B, o)
        if D >= 1:
            continue
        X = average(A, B, o)
        C, _ = polar(X)
        exact = op(C @ B @ C.conj().T - B @ B)
        inter = op(B @ B @ X - X @ B)
        dist = op(C - A)
        lower = op(C0 - A)  # any exact C0 is at distance >= D/2
        assert exact < 1e-9 and inter < 1e-9, (exact, inter)
        assert dist <= 2 * D + 1e-9, (dist, D)
        assert lower >= D / 2 - 1e-9, (lower, D)
        worst_ratio = max(worst_ratio, dist / D)
        print(f"n={n:3d} o={o:2d} Delta={D:.4f} k1={op(A@B@A.conj().T-B@B):.4f} "
              f"||C-A||={dist:.4f} ||C0-A||={lower:.4f} exact={exact:.1e}")
    print(f"max ||C-A||/Delta = {worst_ratio:.4f} (bound 2)")

    # Fine clock: the k=1 defect is small but Delta is maximal, so the
    # conjugator is not correctable with B fixed.  B = diag(w^x) on Z/o and
    # A = (shift x -> x+1) o (exact halving), the twisted pair of the TPC
    # attempts.  A B A^* = w^(-2) B^2, so the k=1 defect is |1-w^2| while
    # Delta = max_k |1-w^(2k)| is about 2.
    for o in (27, 81, 243):
        x = np.arange(o)
        B = np.diag(np.exp(2j * np.pi * x / o))
        inv2 = pow(2, -1, o)
        A = np.zeros((o, o), complex)
        for y in x:
            A[((y * inv2) + 1) % o, y] = 1.0
        k1 = op(A @ B @ A.conj().T - B @ B)
        D = delta_inf(A, B, o)
        print(f"twisted fine clock o={o:3d}: k=1 defect {k1:.4f}, Delta {D:.4f}, "
              f"so every exact C with base B has ||C-A|| >= {D/2:.4f}")


if __name__ == "__main__":
    main()
