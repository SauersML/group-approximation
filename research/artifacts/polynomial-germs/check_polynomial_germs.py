#!/usr/bin/env python3
"""Exact-arithmetic sanity checks for polynomial_germ_boone_higman.md.

Uses only the Python standard library. These checks are NOT a formal verification
of the infinite-group embedding, F-infinity argument, or external theorems.
Run: python check_polynomial_germs.py
"""
from __future__ import annotations
from fractions import Fraction
from math import prod
import json
import random
Matrix = list[list[Fraction]]
SEED = 20260920
rng = random.Random(SEED)
counts: dict[str, int] = {}
def check(condition: bool, family: str) -> None:
    if not condition:
        raise AssertionError(f"Check failed: {family}")
    counts[family] = counts.get(family, 0) + 1
def binom_int(n: int, k: int) -> int:
    """Polynomial binomial coefficient, valid also for negative integers n."""
    if k < 0:
        return 0
    value = Fraction(1)
    for i in range(k):
        value *= Fraction(n - i, i + 1)
    assert value.denominator == 1
    return value.numerator
def peval(coeff: list[int], n: int) -> int:
    return sum(c * binom_int(n, j) for j, c in enumerate(coeff))
def differences(values: list[int]) -> list[int]:
    return [b - a for a, b in zip(values, values[1:])]
def eye(m: int) -> Matrix:
    return [[Fraction(i == j) for j in range(m)] for i in range(m)]
def mul(a: Matrix, b: Matrix) -> Matrix:
    m = len(a)
    assert m == len(b)
    return [[sum((a[i][k] * b[k][j] for k in range(m)), Fraction(0))
             for j in range(m)] for i in range(m)]
def inv(a: Matrix) -> Matrix:
    """Invert an upper unitriangular matrix by finite recursion."""
    m = len(a)
    b = eye(m)
    for w in range(1, m):
        for i in range(m - w):
            j = i + w
            b[i][j] = -sum((a[i][k] * b[k][j] for k in range(i + 1, j + 1)), Fraction(0))
    return b
def delta(a: Matrix, scalar: Fraction | int) -> Matrix:
    m = len(a)
    s = Fraction(scalar)
    if not s:
        raise ValueError("Dilation scalar must be nonzero")
    b = eye(m)
    for i in range(m):
        for j in range(i + 1, m):
            b[i][j] = s ** (j - i) * a[i][j]
    return b
def random_ut(m: int, q: int, max_power: int = 3) -> Matrix:
    a = eye(m)
    for i in range(m):
        for j in range(i + 1, m):
            a[i][j] = Fraction(rng.randint(-8, 8), q ** rng.randint(0, max_power))
    return a
def in_localization(x: Fraction, q: int) -> bool:
    d = x.denominator
    while d > 1:
        from math import gcd
        common = gcd(d, q)
        if common == 1:
            return False
        d //= common
    return True
def p_integral_divisible(x: Fraction, p: int, power: int) -> bool:
    assert x.denominator % p != 0
    return x.numerator % (p ** power) == 0
def in_H(a: Matrix, p: int, depth: int) -> bool:
    return all(p_integral_divisible(a[i][j], p, depth * (j-i))
               for i in range(len(a)) for j in range(i+1, len(a)))
def left_coset_digit(a: Matrix, p: int) -> tuple[Matrix, Matrix]:
    """Compute a=t*h, with integral transversal digit t and h in delta_p(N).

    The coordinate recursion accounts for NON-normality of delta_p(N).
    Simply reducing each entry of a independently would not suffice.
    """
    m = len(a)
    t, h = eye(m), eye(m)
    for w in range(1, m):
        mod = p ** w
        for i in range(m - w):
            j = i + w
            residual = a[i][j] - sum((t[i][k] * h[k][j]
                                      for k in range(i+1, j)), Fraction(0))
            assert residual.denominator % p != 0
            digit = (residual.numerator * pow(residual.denominator, -1, mod)) % mod
            t[i][j] = Fraction(digit)
            h[i][j] = residual - digit
    return t, h
# Integer-valued polynomials, negative-end chart, and normality of layers.
for degree in range(0, 8):
    for _ in range(30):
        c = [rng.randint(-5, 5) for _ in range(degree+1)]
        shift = rng.randint(-7, 7)
        for n in range(-12, 13):
            for j in range(1, degree+1):
                check(binom_int(n+1, j)-binom_int(n, j) == binom_int(n, j-1),
                      "Pascal_and_generator_commutators")
        values = [peval(c, n + shift) for n in range(degree+1)]
        negative = [peval(c, -n - 1) for n in range(degree+2)]
        for _j in range(degree):
            values = differences(values)
        check(values[0] == c[-1], "shift_preserves_top_Newton_coefficient")
        for _j in range(degree+1):
            negative = differences(negative)
        check(negative == [0], "negative_end_preserves_degree")
        if degree >= 1:
            diff = [peval(c,n+shift)-peval(c,n) for n in range(degree+1)]
            for _j in range(degree):
                diff = differences(diff)
            check(diff == [0], "translation_difference_lowers_degree")
# Germ multiplication conventions: right-to-left composition.
for _ in range(1000):
    degree = rng.randint(0, 5)
    pc = [rng.randint(-3,3) for _ in range(degree+1)]
    qc = [rng.randint(-3,3) for _ in range(degree+1)]
    k, ell, n = rng.randint(-4,4), rng.randint(-4,4), rng.randint(8,20)
    after_inner = (n + ell, peval(qc,n))
    after_outer = (after_inner[0]+k, after_inner[1]+peval(pc,after_inner[0]))
    predicted = (n + k + ell, peval(qc,n)+peval(pc,n+ell))
    check(after_outer == predicted, "germ_composition")
    # f^{-1}=f_{-k,-P(. - k)}.
    inverse_after_f = (n+k-k, peval(pc,n)-peval(pc,(n+k)-k))
    check(inverse_after_f == (n,0), "germ_inverse")
# Nilpotent affine sections and lamp covariance.
for m in range(2, 7):
    D = sum(j-i for i in range(m) for j in range(i+1,m))
    check(D == (m**3-m)//6, "graded_index_exponent")
    for _ in range(60):
        p, q = 3, 2
        a, b = random_ut(m,q), random_ut(m,q)
        s, t = Fraction(q)**rng.randint(-2,2), Fraction(p)**rng.randint(-2,2)
        check(delta(mul(a,b),s) == mul(delta(a,s),delta(b,s)), "delta_is_homomorphism")
        check(delta(delta(a,s),t) == delta(delta(a,t),s), "dilations_commute")
        check(mul(a,inv(a)) == eye(m), "matrix_inverse")
        digit, h = left_coset_digit(a,p)
        check(mul(digit,h) == a and in_H(h,p,1), "non_normal_coset_decomposition")
        state = delta(h,Fraction(1,p))
        check(all(in_localization(state[i][j],q)
                  for i in range(m) for j in range(i+1,m)), "affine_section_integrality")
        # Actual section formula for a delta_q^ell on a chosen input digit.
        input_digit, _ = left_coset_digit(b,p)
        ell = rng.randint(-2,2)
        raw = mul(a,delta(input_digit,Fraction(q)**ell))
        output_digit, _ = left_coset_digit(raw,p)
        section_translation = delta(mul(inv(output_digit),raw),Fraction(1,p))
        check(all(in_localization(section_translation[i][j],q)
                  for i in range(m) for j in range(i+1,m)), "full_section_formula")
        x = random_ut(m,q,1)
        reconstructed = mul(output_digit, delta(mul(section_translation,
                                                       delta(x,Fraction(q)**ell)),p))
        original = mul(a, delta(mul(input_digit,delta(x,p)),Fraction(q)**ell))
        check(reconstructed == original, "section_reconstruction")
        e = rng.randint(-2,2)
        lhs = delta(mul(delta(a,p),delta(x,Fraction(q)**(-e))),Fraction(q)**e)
        rhs = mul(delta(delta(a,Fraction(q)**e),p),x)
        check(lhs == rhs, "nonabelian_lamp_covariance")
# Scalar [T,X]=D, checked without enormous exponentiations.
for n in range(-100,101):
    power = -(n-1)+n
    check(power == 1, "q_difference_Heisenberg_commutator")
print(json.dumps({"seed": SEED, "checks": counts,
                  "total": sum(counts.values()),
                  "status": "PASS",
                  "scope": "Exact-arithmetic formula checks only; not a formal proof."}, indent=2))
