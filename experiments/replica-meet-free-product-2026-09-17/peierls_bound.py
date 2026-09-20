"""Peierls bound for bond percolation on the square lattice Z^2.

The origin's open cluster is finite iff some circuit of closed dual edges
surrounds the origin.  A dual circuit of length n surrounding the origin
crosses the positive x-axis at one of at most n dual edges, and from there it
is a self-avoiding dual walk of n - 1 further steps, of which there are at most
4 * 3^(n-2).  So the number of such circuits is at most 4 n 3^(n-2), which we
overestimate by 4 n 3^(n-1).  Circuits have length at least 4.  Hence

    P_p(|C(0)| < infinity) <= sum_{n >= 4} 4 n 3^(n-1) (1-p)^n .

This script evaluates the right side exactly (closed form for the tail of the
series sum n x^(n-1) = 1/(1-x)^2) and by direct summation, for 1 - p = 1/10,
using exact rational arithmetic.  A value < 1 gives theta(p) > 0, so
p_c(Z^2) <= p.
"""
from fractions import Fraction


def peierls_closed_form(q: Fraction) -> Fraction:
    # sum_{n>=4} 4 n 3^(n-1) q^n = 4 q * sum_{n>=4} n x^(n-1), x = 3q
    x = 3 * q
    assert x < 1
    full = 1 / (1 - x) ** 2
    head = sum(n * x ** (n - 1) for n in range(1, 4))
    return 4 * q * (full - head)


def peierls_partial(q: Fraction, terms: int) -> Fraction:
    return sum(4 * n * 3 ** (n - 1) * q ** n for n in range(4, 4 + terms))


if __name__ == "__main__":
    q = Fraction(1, 10)
    exact = peierls_closed_form(q)
    part = peierls_partial(q, 200)
    print("1 - p =", q)
    print("closed form  :", exact, "=", float(exact))
    print("200-term sum :", float(part))
    assert part <= exact
    assert exact < 1
    print("theta(9/10) >=", float(1 - exact), "> 0, so p_c(Z^2) <= 9/10 < 1")
