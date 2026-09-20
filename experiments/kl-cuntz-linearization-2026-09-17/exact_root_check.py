#!/usr/bin/env python3
"""Exact check of the closed-form root of w0 = c t a t a t^-1 in O(3).

X_ij = 1/3 + (2/3) cos(2 pi/9 + 2 pi (2 - i - j)/3),  i, j in {0, 1, 2},
with leaves ordered (00, 01, 1), P_a = leaf permutation of (00 01) and
P_c = leaf permutation of (1 00).  The script verifies, exactly in Q(zeta_9),

  X^T X = I,  X = X^T,  P_c X P_a X P_a X^-1 = I,

and that no 3x3 permutation matrix is a root.  Each entry of the difference
matrices is checked to be exactly zero via its minimal polynomial.
"""
import itertools
import sys

import sympy as sp

y = sp.Symbol("y")
theta = 2 * sp.pi / 9


def perm_matrix(perm):
    m = sp.zeros(3, 3)
    for i, j in enumerate(perm):
        m[j, i] = 1
    return m


def is_exact_zero(e):
    e = sp.expand(sp.expand(e).rewrite(sp.exp))
    if e == 0:
        return True
    return sp.minimal_polynomial(e, y) == y


P_a = perm_matrix([1, 0, 2])
P_c = perm_matrix([2, 1, 0])
X = sp.Matrix(3, 3, lambda i, j: sp.Rational(1, 3)
              + sp.Rational(2, 3) * sp.cos(theta + 2 * sp.pi * ((2 - i - j) % 3) / 3))

checks = {
    "orthogonal": all(is_exact_zero(e) for e in (X.T * X - sp.eye(3))),
    "symmetric": all(is_exact_zero(e) for e in (X - X.T)),
    "root": all(is_exact_zero(e) for e in (P_c * X * P_a * X * P_a * X.T - sp.eye(3))),
    "no_permutation_root": not any(
        (P_c * perm_matrix(list(p)) * P_a * perm_matrix(list(p)) * P_a
         * perm_matrix(list(p)).T) == sp.eye(3)
        for p in itertools.permutations(range(3))),
}
print("X (numeric):", sp.N(X, 12).tolist())
print("trace X =", sp.nsimplify(sp.N(X.trace(), 40)), " det X =", sp.nsimplify(sp.N(X.det(), 40)))
for k, v in checks.items():
    print(k, v)
ok = all(checks.values())
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
