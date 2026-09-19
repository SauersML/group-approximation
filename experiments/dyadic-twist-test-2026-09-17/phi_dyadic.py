"""Calibration for step 6(B) of lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure-proof.

nu = sum_k w_k delta_{2^-k}.  Phi(n) = sum_k w_k |e(n 2^-k) - 1|^2 = sum_k w_k 4 sin^2(pi n / 2^k).

Worry checked: for FINITE nu, Phi is 2-adically continuous, so Phi(1 + 2^J) -> Phi(1) (bounded,
not proper).  Step 6(B) survives because its weights w_k = R_k^{-1/2} tend to infinity: nu has
infinite mass, and the single term k = J + 2 already gives Phi(1 + 2^J) >= 2 w_{J+2}.
Exact arithmetic on n / 2^k mod 1 is used, so large n are safe.
"""
from fractions import Fraction
import math

K = 80


def phi(n, w):
    s = 0.0
    for k in range(1, K + 1):
        x = Fraction(n % (2 ** k), 2 ** k)
        s += w(k) * 4 * math.sin(math.pi * float(x)) ** 2
    return s


cases = {
    "finite  w_k = 2^-k": lambda k: 2.0 ** (-k),
    "step6B  w_k = k   ": lambda k: float(k),  # R_k ~ 4^-k gives w_k ~ 2^k; k is a slower test
    "step6B  w_k = 2^(k/2)": lambda k: 2.0 ** (k / 2),
}

if __name__ == "__main__":
    for name, w in cases.items():
        row = []
        for J in (4, 8, 16, 32, 60):
            n = 1 + 2 ** J
            row.append(f"J={J}:{phi(n, w):.4g} (2w_(J+2)={2 * w(J + 2):.4g})")
        print(name, " | ".join(row))
    print("finite nu: Phi(1) =", round(phi(1, cases["finite  w_k = 2^-k"]), 6))
