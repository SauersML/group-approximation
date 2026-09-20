#!/usr/bin/env python3
"""Checks for h-prime-mf-head-iff-alpha-periodic-w-models.

Part A (exact, over J = F_2<S,T|TS=1>, normal form S^i T^j): inside
H' = M_2(J) x| (EL_2(J) x <c>) <= EL_4(J), with c = r2 = x_43(S) x_34(1)
= diag(1, 1, C^{-1}), C = [[1+S,1],[S,1]], the one-generator trap holds:
    [g,c] = 1,  g u g^-1 = (c u c^-1)(c^-1 u c),  [e,u] = [e,c] = 1,
    [e, g^-1 u g] = x_13(Q)  (the head).
So the witness of p22-double-parabolic-is-not-lef lives in <g,e,u,c> <= H'
with r1 removed. Also: the c-orbit of u is infinite (the S-degree of
E_11 C^n is n), so no finite window of W is alpha-stable.

Part B (numerical, numpy): the block-shift identity used in the proof.
For arbitrary unitaries X_n = theta(alpha^n w) (n = 0..m) and V, with
rho(w) = diag(X_0..X_{m-1}) and R the twisted cyclic shift
(R xi)_n = xi_{n+1} (n < m-1), (R xi)_{m-1} = V* xi_0,
R rho(w) R* = diag(X_1, .., X_{m-1}, V* X_0 V) exactly, so
||R rho(w) R* - rho(alpha w)|| = ||V* X_0 V - X_m||.
Exit status 0 iff every check passes.
"""
import importlib.util
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
PH = os.path.join(HERE, "..", "p22-conjugation-pigeonhole-2026-09-17",
                  "pigeonhole_check.py")
spec = importlib.util.spec_from_file_location("ph", PH)
ph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ph)


def part_a(check):
    I = ph.mat_id()
    c = ph.r2
    g, e, u = ph.g, ph.e, ph.u
    C = ph.val(c)
    check("c = diag(1,1,C^-1), C^-1 = [[1,1],[S,1+S]]",
          all(C[2 + r][2 + k] ==
              (((ph.ONE, ph.ONE), (ph.S, ph.jadd(ph.ONE, ph.S)))[r][k])
              for r in range(2) for k in range(2)))
    check("[g,c] = 1", ph.val(ph.comm(g, c)) == I)
    check("[e,c] = 1", ph.val(ph.comm(e, c)) == I)
    check("[e,u] = 1", ph.val(ph.comm(e, u)) == I)
    lhs = ph.val(ph.conj(g, u))
    rhs = ph.val(ph.cat(ph.conj(c, u), ph.conj(ph.inv(c), u)))
    check("g u g^-1 = (c u c^-1)(c^-1 u c)", lhs == rhs)
    x = ph.conj(ph.inv(g), u)
    check("[e, g^-1 u g] = x_13(Q) != 1",
          ph.val(ph.comm(e, x)) == ph.elem(1, 3, ph.Q) != I)
    # c-orbit of u: c^n u c^-n = n(E_11 C^{-n})-type rows; degree grows
    w = []
    ok = True
    for n in range(1, 13):
        w = ph.cat(w, c)
        M = ph.val(ph.conj(w, u))
        deg = max(i + j for ent in (M[0][2], M[0][3]) for (i, j) in ent)
        ok = ok and deg == n and all(j == 0 for ent in (M[0][2], M[0][3])
                                     for (_, j) in ent)
        ok = ok and M[1][2] == ph.ZERO and M[1][3] == ph.ZERO
    check("c^n u c^-n has first row in F_2[S]^2 of S-degree n (n<=12)", ok)


def haar(d, rng):
    z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / abs(np.diag(r)))


def part_b(check):
    rng = np.random.default_rng(17)
    ok = True
    for (m, d) in [(1, 3), (2, 2), (4, 3), (7, 2)]:
        X = [haar(d, rng) for _ in range(m + 1)]
        V = haar(d, rng)
        rho = np.zeros((m * d, m * d), complex)
        rho_a = np.zeros((m * d, m * d), complex)
        for n in range(m):
            rho[n*d:(n+1)*d, n*d:(n+1)*d] = X[n]
            rho_a[n*d:(n+1)*d, n*d:(n+1)*d] = X[n + 1]
        R = np.zeros((m * d, m * d), complex)
        for n in range(m - 1):
            R[n*d:(n+1)*d, (n+1)*d:(n+2)*d] = np.eye(d)
        R[(m-1)*d:m*d, 0:d] = V.conj().T
        ok = ok and np.allclose(R @ R.conj().T, np.eye(m * d))
        err = np.linalg.norm(R @ rho @ R.conj().T - rho_a, 2)
        seam = np.linalg.norm(V.conj().T @ X[0] @ V - X[m], 2)
        ok = ok and abs(err - seam) < 1e-9
    check("block shift: ||R rho R* - rho o alpha|| = seam error", ok)


def main():
    good = True

    def check(name, cond):
        nonlocal good
        print("%-62s %s" % (name, "ok" if cond else "FAIL"))
        good = good and bool(cond)

    part_a(check)
    part_b(check)
    print("ALL CHECKS PASS" if good else "SOME CHECK FAILED")
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
