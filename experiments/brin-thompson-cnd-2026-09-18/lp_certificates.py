#!/usr/bin/env python3
"""Certified failure of conditional negative definiteness for the l^p norm on Z^3, p > 2.

Companion to the l^infinity certificates of
experiments/brin-thompson-cnd-2026-09-17/zcube_obstruction.py.

Background. On the Z^3 of disjoint-support baker maps b_00, b_01, b_1 inside 2V
(see research/brin-thompson-nv-max-type-size-functions-are-not-cnd) a size function
that aggregates the three pieces by an l^p norm has psi(g(w)) ~ kappa ||w||_p.
The l^infinity case p = oo is killed there.  This script certifies the same failure
for every p in a tested list with p > 2, and confirms that no failure occurs for
p <= 2 (where l_p^3 embeds isometrically in L^1 and the norm is of negative type).

Method.  On a grid S = {-k..k}^3 take the kernel K(x, y) = ||x - y||_p.  Pairs are
classified by the sorted triple t = (a <= b <= c) of absolute coordinate differences;
the class counts  N_t = sum over pairs in class t of c_x c_y  are INTEGERS once the
coefficient vector c is integral and zero-sum.  Then

    Q_p = sum_t N_t * (a^p + b^p + c^p)^(1/p)

is evaluated in 80-digit Decimal arithmetic.  Q_p > 0 for a zero-sum c certifies that
K is not conditionally negative definite on S, hence not on Z^3.

Combined with Schoenberg's power trick (Step 4 of
brin-thompson-nv-max-type-size-functions-are-not-cnd-proof: K cnd => K^alpha cnd for
0 < alpha < 1), a certificate for K = ||x - y||_p also kills ||x - y||_p^beta for all
beta >= 1.

Usage: python3 lp_certificates.py [--k 3] [--write]
       python3 lp_certificates.py --verify        (integers + Decimal only)
"""
import argparse
import itertools
import json
import os
from decimal import Decimal, getcontext

import numpy as np

getcontext().prec = 80

HERE = os.path.dirname(os.path.abspath(__file__))
CERT_FILE = os.path.join(HERE, "lp_certificates.json")

# (p, grid half-width k).  The grid needed grows as p decreases to 2; p = 2 is the
# control, where l_2^3 is Euclidean and the kernel IS cnd, so no failure exists.
P_LIST = [("2.0", 5), ("2.15", 5), ("2.25", 4), ("2.5", 2), ("3.0", 2),
          ("4.0", 2), ("6.0", 2), ("10.0", 2)]


def dec_pow(base, expo):
    """base ** expo in Decimal, base > 0."""
    return (Decimal(expo) * Decimal(base).ln()).exp()


def lp_dist(t, p):
    """Decimal value of (a^p + b^p + c^p)^(1/p) for an integer triple t."""
    s = sum(dec_pow(v, p) for v in t if v > 0)
    return dec_pow(s, Decimal(1) / Decimal(p))


def classes(k):
    """All sorted absolute-difference triples occurring on {-k..k}^3, excluding (0,0,0)."""
    out = set()
    for t in itertools.product(range(0, 2 * k + 1), repeat=3):
        if any(t):
            out.add(tuple(sorted(t)))
    return sorted(out)


def top_zero_sum(K):
    """Largest eigenvalue/eigenvector of K restricted to the zero-sum subspace."""
    n = K.shape[0]
    J = np.eye(n) - np.ones((n, n)) / n
    M = J @ K @ J
    M = (M + M.T) / 2
    w, V = np.linalg.eigh(M)
    return w[-1], V[:, -1]


def class_counts(pts, c, k):
    """N_t for every sorted absolute-difference triple, as exact Python integers."""
    N = {}
    n = len(pts)
    for i in range(n):
        xi = pts[i]
        ci = c[i]
        if ci == 0:
            continue
        for j in range(n):
            cj = c[j]
            if cj == 0 or i == j:
                continue
            t = tuple(sorted(abs(a - b) for a, b in zip(xi, pts[j])))
            N[t] = N.get(t, 0) + ci * cj
    return {t: v for t, v in N.items() if v != 0}


def quad(N, p):
    return sum(Decimal(v) * lp_dist(t, p) for t, v in N.items())


def search(k, p, scale=10 ** 6):
    pts = list(itertools.product(range(-k, k + 1), repeat=3))
    P = np.array(pts, dtype=float)
    diff = np.abs(P[:, None, :] - P[None, :, :])
    K = (diff ** float(p)).sum(-1) ** (1.0 / float(p))
    lam, vec = top_zero_sum(K)
    c = [int(round(scale * x)) for x in vec]
    i0 = max(range(len(c)), key=lambda i: abs(c[i]))
    c[i0] -= sum(c)
    assert sum(c) == 0
    N = class_counts(pts, c, k)
    return pts, c, N, quad(N, p), lam


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--verify", action="store_true")
    args = ap.parse_args()

    if args.verify:
        with open(CERT_FILE) as fh:
            certs = json.load(fh)
        for cert in certs:
            k, p, c = cert["k"], cert["p"], cert["c"]
            pts = list(itertools.product(range(-k, k + 1), repeat=3))
            assert len(pts) == len(c) and sum(c) == 0
            N = class_counts(pts, c, k)
            Q = quad(N, p)
            mass = sum(abs(Decimal(v)) * lp_dist(t, p) for t, v in N.items())
            margin = mass * Decimal(10) ** (-70)
            print("verify: p=%-5s k=%d points=%3d Q_p=%s  %s"
                  % (p, k, len(pts), ("%.10e" % Q),
                     "CERTIFIED" if Q > margin else "no failure (expected for p<=2)"))
        return

    out = []
    for p, k in P_LIST:
        pts, c, N, Q, lam = search(k, p)
        mass = sum(abs(Decimal(v)) * lp_dist(t, p) for t, v in N.items())
        margin = mass * Decimal(10) ** (-70)
        ok = Q > margin
        print("p=%-5s k=%d  top zero-sum eigenvalue %+.6e   Q_p=%+.6e   %s"
              % (p, k, lam, Q, "NOT CND (certified)" if ok else "no failure found"))
        if ok:
            out.append({"k": k, "p": p, "c": c})
    if args.write:
        with open(CERT_FILE, "w") as fh:
            json.dump(out, fh)
        print("wrote %d certificates to %s" % (len(out), CERT_FILE))


if __name__ == "__main__":
    main()
