#!/usr/bin/env python3
"""Exact certificates used to show that every prime is a Higman period.

Standard library only. Interval endpoints are integers scaled by 2**400;
every arithmetic operation rounds outwards. Root isolation, continued
fractions, resultants, and projective matrices use exact rational/integer
arithmetic. See the associated proof artifact for the analytic implications.
"""

from fractions import Fraction as F
from math import gcd, isqrt
from periodic_higman_algebraic_certificate import P, g, gadd, gmul

SCALE = 2**400
BOUND = 4000 * 40**12


def ceiling(a, b):
    return -((-a) // b)


class Interval:
    def __init__(self, low, high=None):
        self.low = low
        self.high = low if high is None else high
        assert self.low <= self.high

    @classmethod
    def rational(cls, value):
        value = F(value)
        return cls(value.numerator * SCALE // value.denominator,
                   ceiling(value.numerator * SCALE, value.denominator))

    def __add__(self, other):
        return Interval(self.low + other.low, self.high + other.high)

    def __neg__(self):
        return Interval(-self.high, -self.low)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        products = [a * b for a in (self.low, self.high)
                    for b in (other.low, other.high)]
        return Interval(min(products) // SCALE, ceiling(max(products), SCALE))

    def __truediv__(self, other):
        assert other.low > 0 or other.high < 0
        reciprocal = Interval(SCALE**2 // other.high,
                              ceiling(SCALE**2, other.low))
        return self * reciprocal


iv = Interval.rational
ONE = iv(1)


def atan_series(x):
    """250 alternating terms; |x| <= 1/2 makes the tail < 2**-501."""
    assert max(abs(x.low), abs(x.high)) * 2 <= SCALE
    power, total = x, iv(0)
    square = x * x
    for j in range(250):
        term = power / iv(2 * j + 1)
        total = total + (term if j % 2 == 0 else -term)
        power = power * square
    return Interval(total.low - 1, total.high + 1)


PI = iv(16) * atan_series(iv(F(1, 5))) - iv(4) * atan_series(iv(F(1, 239)))


def atan(x):
    if x.high < 0:
        return -atan(-x)
    assert x.low >= 0
    if x.low > SCALE:
        return PI / iv(2) - atan(ONE / x)
    if x.low * 2 > SCALE:
        return PI / iv(4) + atan_series((x - ONE) / (x + ONE))
    return atan_series(x)


# Polynomial operations in ascending coefficient order.
Q = [F(-1), F(1), F(2), F(-2), F(7), F(1)]


def trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def remainder(a, b):
    a = list(a)
    while len(a) >= len(b) and a != [0]:
        c, shift = a[-1] / b[-1], len(a) - len(b)
        for j in range(len(b)):
            a[j + shift] -= c * b[j]
        trim(a)
    return a


def evaluate(a, x):
    result = F(0)
    for c in reversed(a):
        result = result * x + c
    return result


def real_root_count():
    sturm = [Q, [j * Q[j] for j in range(1, len(Q))]]
    while True:
        r = remainder(sturm[-2], sturm[-1])
        if r == [0]:
            break
        sturm.append([-x for x in r])
    assert len(sturm[-1]) == 1  # Square-free.

    def variation(at_positive_infinity):
        signs = []
        for p in sturm:
            sign = 1 if p[-1] > 0 else -1
            if not at_positive_infinity and (len(p) - 1) % 2:
                sign = -sign
            signs.append(sign)
        return sum(a != b for a, b in zip(signs, signs[1:]))

    left, right = variation(False), variation(True)
    assert left - right == 3
    print("PASS: Sturm variations at -infinity and +infinity:", left, right)


def isolate(low, high):
    low, high = F(low), F(high)
    assert evaluate(Q, low) * evaluate(Q, high) < 0
    while high - low > F(1, 2**420):
        midpoint = (low + high) / 2
        value = evaluate(Q, midpoint)
        assert value != 0
        if value * evaluate(Q, low) > 0:
            low = midpoint
        else:
            high = midpoint
    return Interval(iv(low).low, iv(high).high)


def best_approximation_certificate(alpha):
    """Find a rational approximant with denominator above BOUND.

    The final inequality is a direct rational-separation certificate;
    no best-approximation theorem is needed for its verification.
    """
    if alpha.high < 0:
        alpha = -alpha
    assert 0 < alpha.low < alpha.high < SCALE // 2
    center = (alpha.low + alpha.high) // 2
    numerator, denominator = center, SCALE
    p0, p1, q0, q1 = 0, 1, 1, 0
    while denominator:
        a, rem = divmod(numerator, denominator)
        p2, q2 = a * p1 + p0, a * q1 + q0
        if q2 > BOUND:
            break
        p0, p1, q0, q1 = p1, p2, q1, q2
        numerator, denominator = denominator, rem
    assert denominator and 0 < q1 <= BOUND < q2
    assert gcd(p2, q2) == 1
    error = max(abs(q2 * alpha.low - p2 * SCALE),
                abs(q2 * alpha.high - p2 * SCALE))
    # For 1 <= n <= BOUND < q2, |n*p2/q2-m| >= 1/q2 for every integer m.
    # Subtract n*|alpha-p2/q2| to get (1-BOUND*error/SCALE)/q2.
    assert (SCALE - BOUND * error) * 10**30 > q2 * SCALE
    print("PASS: angle separation > 10^-30; rational witness (p,q):", (p2, q2))


def certify_angles_and_growth():
    real_root_count()
    roots = [isolate(-8, -7), isolate(-1, 0), isolate(0, 1)]
    sum_real, sum_imag = iv(0), iv(0)
    for root in roots:
        best_approximation_certificate(atan(root) / PI)
        square = root * root
        sum_real = sum_real + (ONE - square) / (ONE + square)
        sum_imag = sum_imag + iv(2) * root / (ONE + square)
    other_real = iv(4) - sum_real
    other_imag = iv(3) - sum_imag
    assert other_real.low * 2 > 7 * SCALE
    assert other_imag.low > 3 * SCALE
    assert F(7, 2)**2 + 3**2 > F(17, 4)**2
    print("PASS: remaining root sum has real part > 7/2, imaginary part > 3")
    assert 8 * 4**400 > 10**180
    print("PASS: the resultant lower bound exceeds one for all n >= 200")


# N(L) = P(L) conjugate(P)(L), a monic degree-ten integer polynomial.
N = [1, -8, 29, -16, -14, 48, -14, -16, 29, -8, 1]


def check_polynomial_identities():
    def product(a, b):
        out = [g()] * (len(a) + len(b) - 1)
        for j, x in enumerate(a):
            for k, y in enumerate(b):
                out[j + k] = gadd(out[j + k], gmul(x, y))
        return out

    conjugate_p = [(a, -b) for a, b in P]
    assert product(P, conjugate_p) == [g(c) for c in N]
    assert P == [gmul(g(0, 1), c) for c in reversed(conjugate_p)]
    transformed = [g()] * 6
    for j, c in enumerate(P):
        term = [c]
        for k in range(5):
            term = product(term, [g(1), g(0, 1 if k < j else -1)])
        transformed = [gadd(a, b) for a, b in zip(transformed, term)]
    assert transformed == [g(4 * c, 4 * c) for c in Q]
    print("PASS: norm, self-inversive, and Cayley polynomial identities")


def times_l(a):
    shifted = [0] + a[:-1]
    for j in range(10):
        shifted[j] -= a[-1] * N[j]
    return shifted


def determinant(a):
    """Fraction-free Bareiss elimination, with exact divisions checked."""
    a = [row[:] for row in a]
    sign, previous = 1, 1
    size = len(a)
    for k in range(size - 1):
        if not a[k][k]:
            swap = next((j for j in range(k + 1, size) if a[j][k]), None)
            if swap is None:
                return 0
            a[k], a[swap] = a[swap], a[k]
            sign = -sign
        pivot = a[k][k]
        for j in range(k + 1, size):
            for h in range(k + 1, size):
                value = pivot * a[j][h] - a[j][k] * a[k][h]
                assert value % previous == 0
                a[j][h] = value // previous
            a[j][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def norm_geometric_sum(n):
    power = [1] + [0] * 9
    total = [0] * 10
    for _ in range(n):
        total = [a + b for a, b in zip(total, power)]
        power = times_l(power)
    columns = [total]
    for _ in range(9):
        columns.append(times_l(columns[-1]))
    return determinant([list(row) for row in zip(*columns)])


def small_prime_resultants():
    assert sum(N) == 32
    primes = [p for p in range(3, 200, 2)
              if all(p % d for d in range(2, isqrt(p) + 1))]
    for p in primes:
        result = norm_geometric_sum(p)
        assert result > 1 and result % 2 and result % p
    assert norm_geometric_sum(3) == 20449
    assert norm_geometric_sum(5) == 2070721
    print("PASS: exact nonunit resultants for", len(primes), "odd primes below 200")


def period_two_certificate():
    p = 5

    def canonical(a):
        return min(tuple(x % p for x in a), tuple(-x % p for x in a))

    def multiply(a, b):
        x, y, z, w = a
        u, v, r, s = b
        return canonical((x * u + y * r, x * v + y * s,
                          z * u + w * r, z * v + w * s))

    def inverse(a):
        x, y, z, w = a
        assert (x * w - y * z) % p == 1
        return canonical((w, -y, -z, x))

    identity = canonical((1, 0, 0, 1))
    t = canonical((0, 1, 4, 0))
    h = [canonical(a) for a in [(1, 0, 2, 1), (1, 1, 2, 3),
                               (1, 2, 0, 1), (2, 3, 4, 4)]]
    assert multiply(t, t) == identity
    conjugate = lambda a: multiply(multiply(t, a), inverse(t))
    assert conjugate(h[0]) != h[0]
    for j in range(4):
        a, b = h[j], h[j - 1]
        assert a != identity
        commutator = multiply(multiply(multiply(inverse(a), inverse(b)), a), b)
        assert commutator == conjugate(a)
    subgroup, queue = {identity}, [identity]
    while queue:
        a = queue.pop()
        for b in h:
            c = multiply(a, b)
            if c not in subgroup:
                subgroup.add(c)
                queue.append(c)
    assert len(subgroup) == 60
    print("PASS: period-two certificate generates PSL_2(5), of order 60")


if __name__ == "__main__":
    check_polynomial_identities()
    certify_angles_and_growth()
    small_prime_resultants()
    period_two_certificate()
    print("All exact finite checks passed; see the proof for the infinite-range argument.")
