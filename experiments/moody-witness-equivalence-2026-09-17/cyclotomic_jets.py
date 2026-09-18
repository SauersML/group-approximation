#!/usr/bin/env python3
"""Exact checks for `brunnian-burau-kernel-mod-cyclotomic-products-nontrivial`.

Conventions as in experiments/zp-burau-parity-t-minus-one-2026-09-16/burau_minus_one.py
(unreduced Burau rho_4(sigma_i) = I + [[1-t, t],[1, 0]] block, words are lists of +-i).

Checks (all must print True):
 1. P := (rho_4(Delta_3^2) - I) / (t^3 - 1) is an idempotent 4x4 matrix over Q(t) and
    (1 + t + t^2) P has entries in Z[t^{+-1}].  Hence rho_4(Delta_3^{2k}) = I + (t^{3k} - 1) P
    and rho_4(Delta_3^{2k}) = I mod Q_k := (t^{3k} - 1)/(1 + t + t^2) (proof in the claim).
    We also confirm rho_4(Delta_3^{2k}) - I = (t^{3k}-1) P directly for k = 1..6.
 2. The full twist identity Delta_4^2 = Delta_3^2 * A14 A24 A34 holds in B_4, checked on the
    (faithful) Artin action on F_4 in both handedness conventions and both composition orders.
 3. The Brunnian braid b = [A14, [A24, A34]] and the level-one element
    Phi0 = [Delta_3^4, b] (the braid of burau-minus-one-kernel-meets-brunnian-four-braids)
    satisfy rho_4(b) = I mod (t-1) and rho_4(Phi0) = I mod (t-1) Q_2 = (t-1)^2 (t+1)(t^2-t+1).
 4. X2 := [Delta_3^4, Phi0] has rho_4(X2) != I and rho_4(X2) = I mod (t-1) Q_2^2, so in
    particular mod (t+1)^2 (second-order jet at t = -1 vanishes).
 5. Y := [Delta_3^10, Phi0] has rho_4(Y) != I and rho_4(Y) = I mod (t-1) Q_2 Q_5, where
    Q_5 = (t-1)(t^4+t^3+t^2+t+1)(Phi_15).
 6. Negative control: rho_4(Phi0) is NOT = I mod (t+1)^2 and NOT = I mod (t^2+t+1).
"""
import os
import sys

import sympy as sp

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "zp-burau-parity-t-minus-one-2026-09-16"))
from burau_minus_one import rho, comm, A, artin, compose, is_ident  # noqa: E402

t = sp.symbols("t")


def to_sympy(R):
    return sp.Matrix([[sum(c * t ** e for e, c in x.items()) for x in row] for row in R])


def divisible(M, F):
    """Every entry of M (Laurent polynomials) is divisible by polynomial F in Z[t^{+-1}]."""
    for x in M:
        x = sp.together(sp.expand(x))
        num, den = sp.fraction(x)
        # den is a power of t, a unit in Z[t^{+-1}]; F is coprime to t, so test num only
        assert sp.Poly(den, t).is_monomial
        q, r = sp.div(sp.Poly(num, t), sp.Poly(F, t))
        if not r.is_zero:
            return False
    return True


def main():
    ok = True
    n = 4
    I4 = sp.eye(4)
    D3sq = [1, 2] * 3
    R1 = to_sympy(rho(n, D3sq))
    P = ((R1 - I4) / (t ** 3 - 1)).applyfunc(sp.simplify)
    idem = (P * P - P).applyfunc(sp.simplify) == sp.zeros(4)
    integral = all(sp.fraction(sp.together(sp.simplify((1 + t + t ** 2) * x)))[1].is_Pow
                   or sp.fraction(sp.together(sp.simplify((1 + t + t ** 2) * x)))[1].is_Symbol
                   or sp.fraction(sp.together(sp.simplify((1 + t + t ** 2) * x)))[1] == 1
                   for x in P)
    powers = True
    for k in range(1, 7):
        Rk = to_sympy(rho(n, D3sq * k))
        powers &= (Rk - I4 - (t ** (3 * k) - 1) * P).applyfunc(sp.simplify) == sp.zeros(4)
    print("1. P idempotent:", idem, "; (1+t+t^2)P integral:", integral,
          "; rho(Delta_3^{2k}) = I + (t^{3k}-1)P for k=1..6:", powers)
    print("   P =", P.applyfunc(sp.factor).tolist())
    ok &= idem and integral and powers

    D4sq = [1, 2, 3] * 4
    z = A(1, 4) + A(2, 4) + A(3, 4)
    c2 = True
    for hand in (1, -1):
        for order in (0, 1):
            c2 &= artin(n, D4sq, hand, order) == artin(n, D3sq + z, hand, order)
    print("2. Delta_4^2 = Delta_3^2 A14 A24 A34 (Artin action, all conventions):", c2)
    ok &= c2

    b = comm(A(1, 4), comm(A(2, 4), A(3, 4)))
    T2 = D3sq * 2
    Phi0 = comm(T2, b)
    Rb = to_sympy(rho(n, b))
    Rphi = to_sympy(rho(n, Phi0))
    Q2 = sp.cancel((t ** 6 - 1) / (1 + t + t ** 2))
    Q5 = sp.cancel((t ** 15 - 1) / (1 + t + t ** 2))
    c3 = divisible(Rb - I4, t - 1) and divisible(Rphi - I4, (t - 1) * Q2)
    print("3. rho(b)=I mod (t-1):", divisible(Rb - I4, t - 1),
          "; rho(Phi0)=I mod (t-1)Q_2:", divisible(Rphi - I4, (t - 1) * Q2),
          "; Q_2 =", sp.factor(Q2))
    ok &= c3

    X2 = comm(T2, Phi0)
    RX2 = rho(n, X2)
    SX2 = to_sympy(RX2)
    c4 = (not is_ident(RX2)) and divisible(SX2 - I4, (t - 1) * Q2 ** 2) and \
        divisible(SX2 - I4, (t + 1) ** 2)
    print("4. X2 = [Delta_3^4, Phi0]: length", len(X2), "; rho != I:", not is_ident(RX2),
          "; = I mod (t-1)Q_2^2:", divisible(SX2 - I4, (t - 1) * Q2 ** 2))
    ok &= c4

    T5 = D3sq * 5
    Y = comm(T5, Phi0)
    RY = rho(n, Y)
    SY = to_sympy(RY)
    c5 = (not is_ident(RY)) and divisible(SY - I4, (t - 1) * Q2 * Q5)
    print("5. Y = [Delta_3^10, Phi0]: length", len(Y), "; rho != I:", not is_ident(RY),
          "; = I mod (t-1)Q_2 Q_5:", divisible(SY - I4, (t - 1) * Q2 * Q5),
          "; Q_5 =", sp.factor(Q5))
    ok &= c5

    c6 = (not divisible(Rphi - I4, (t + 1) ** 2)) and (not divisible(Rphi - I4, t ** 2 + t + 1))
    print("6. control: Phi0 not = I mod (t+1)^2:", not divisible(Rphi - I4, (t + 1) ** 2),
          "; not = I mod t^2+t+1:", not divisible(Rphi - I4, t ** 2 + t + 1))
    ok &= c6
    print("ALL CHECKS PASS:", ok)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
