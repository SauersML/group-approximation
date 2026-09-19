#!/usr/bin/env python3
"""Exact certification of fixed-dimension commutator ratios for Thompson's F.

Input: a float witness (U, W) in U(n) saved by defect_profile.py --save.  Every word used here
(c = [a,b], R1 = [ab^-1, a^-1ba], R2 = [ab^-1, a^-2ba^2]) is a product of commutators, so it is
invariant under U -> wU, W -> w'W for unit scalars; we rotate so that -1 is far from both spectra.

Rigorous step: K = Cayley^-1(U) is rounded to a skew-Hermitian matrix with entries in Q(i)
(denominator D), and U' = (I-K)(I+K)^-1 is rebuilt EXACTLY as a real 2n x 2n orthogonal matrix
over Q (realification Z = A + iB -> [[A,-B],[B,A]]; normalized traces are preserved, and the
realified pair is a pair in U(n) because K keeps the complex structure).  Then e(g) = 2 - 2 tr(g)/(2n)
is an exact rational, and we check  e(c) >= B^2 * max(e(R1), e(R2))  exactly.  A pass proves
C_n(F) >= B.  Nothing here is an upper bound.

Usage: python3 certify_ratio.py wit_F_n16_tau1.8.npy --den 4096 --bound 3.5
"""

import argparse
import json
from fractions import Fraction

import numpy as np
from flint import fmpq, fmpq_mat


def best_phase(U):
    ang = np.angle(np.linalg.eigvals(U))
    grid = np.linspace(-np.pi, np.pi, 721)
    # angular distance of the rotated spectrum from pi (eigenvalue -1); maximize the minimum
    score = [np.min(np.pi - np.abs(np.angle(np.exp(1j * (ang + t))))) for t in grid]
    return np.exp(1j * grid[int(np.argmax(score))])


def rounded_realified_K(U, den):
    n = U.shape[0]
    eye = np.eye(n)
    K = (eye - U) @ np.linalg.inv(eye + U)
    H = -1j * K
    H = 0.5 * (H + H.conj().T)
    Hr = np.round(H.real * den).astype(object)
    Hi = np.round(H.imag * den).astype(object)
    Hr = np.triu(Hr) + np.triu(Hr, 1).T  # symmetric
    Hi = np.triu(Hi, 1) - np.triu(Hi, 1).T  # antisymmetric, zero diagonal
    # K = i H = -Hi + i Hr, realified [[A,-B],[B,A]] with A = -Hi, B = Hr
    A, B = -Hi, Hr
    top = np.hstack([A, -B])
    bot = np.hstack([B, A])
    M = np.vstack([top, bot])
    m = 2 * n
    return fmpq_mat(m, m, [fmpq(int(M[i, j]), den) for i in range(m) for j in range(m)])


def exact_orth(U, den):
    Kq = rounded_realified_K(U, den)
    m = Kq.nrows()
    eye = fmpq_mat(m, m, [fmpq(1) if i == j else fmpq(0) for i in range(m) for j in range(m)])
    O = (eye - Kq) * (eye + Kq).inv()
    assert O * O.transpose() == eye
    return O, eye


def e_exact(g):
    m = g.nrows()
    tr = sum((g[i, i] for i in range(m)), fmpq(0))
    return 2 - 2 * tr / m


def comm(X, Y):
    return X * Y * X.transpose() * Y.transpose()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("witness")
    ap.add_argument("--den", type=int, default=4096)
    ap.add_argument("--bound", type=str, default=None, help="terminating decimal B to certify")
    args = ap.parse_args()
    U, W = np.load(args.witness)
    U = U * best_phase(U)
    W = W * best_phase(W)
    a, _ = exact_orth(U, args.den)
    b, _ = exact_orth(W, args.den)
    ai = a.transpose()
    x = a * b.transpose()
    y = ai * b * a
    z = ai * ai * b * a * a
    ec, e1, e2 = e_exact(comm(a, b)), e_exact(comm(x, y)), e_exact(comm(x, z))
    emax = max(e1, e2)
    ratio = float(ec) / float(emax)
    out = {"witness": args.witness, "n": U.shape[0], "den": args.den, "e_c": float(ec),
           "e_R1": float(e1), "e_R2": float(e2), "ratio_sq": ratio, "C_lower": ratio ** 0.5}
    if args.bound:
        Bq = Fraction(args.bound)
        B = fmpq(Bq.numerator, Bq.denominator)
        out["bound"] = args.bound
        out["exact_check_holds"] = bool(ec >= B * B * emax)
    print(json.dumps(out))


if __name__ == "__main__":
    main()
