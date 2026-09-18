"""Witnesses: distributions with equal (or larger) Shannon entropy but larger collision sum.

Pair A (Bowen, equal entropy): p = (1/2,1/4,1/4) and q = (a,a,1-2a) with a in (1/3,1/2)
chosen so H(q) = H(p) = 1.5 bits.  Located by bisection with a certified bracket
(H(a,a,1-2a) is strictly decreasing in a on [1/3,1/2]).  Reports sum p^2, sum q^2, Renyi-2.

Pair B (Seward, strictly larger entropy): p = (1/3,1/3,1/3), q = (3/5,1/10,1/10,1/10,1/10).
"""
from decimal import Decimal, getcontext

getcontext().prec = 60
LN2 = Decimal(2).ln()


def mpf(x):
    return Decimal(x)


def log(x, base):
    return Decimal(x).ln() / LN2


def nstr(x, k):
    return format(+x, ".%dg" % k)


def H(v):  # Shannon entropy in bits
    return -sum(x * log(x, 2) for x in v if x > 0)


def col(v):
    return sum(x * x for x in v)


p = [mpf(1) / 2, mpf(1) / 4, mpf(1) / 4]
target = H(p)
lo, hi = mpf(1) / 3, mpf(1) / 2  # H = log2 3 > 1.5 at lo, H = 1 < 1.5 at hi


def f(a):
    return H([a, a, 1 - 2 * a]) - target


assert f(lo) > 0 and f(hi) < 0
for _ in range(160):
    mid = (lo + hi) / 2
    if f(mid) > 0:
        lo = mid
    else:
        hi = mid
qlo, qhi = [lo, lo, 1 - 2 * lo], [hi, hi, 1 - 2 * hi]
# sum q^2 = 6a^2 - 4a + 1 is increasing for a > 1/3, so the root's value lies in [col(qlo), col(qhi)]
print("Pair A: a in [%s, %s]" % (nstr(lo, 30), nstr(hi, 30)))
print("  H(p) = %s bits,  H(q) - H(p) in [%s, %s]" % (nstr(target, 20), nstr(f(hi), 5), nstr(f(lo), 5)))
print("  sum p^2 = %s,  sum q^2 in [%s, %s]" % (nstr(col(p), 20), nstr(col(qlo), 20), nstr(col(qhi), 20)))
print("  1 - sum p^2 = %s  vs  1 - sum q^2 in [%s, %s]" % (nstr(1 - col(p), 20), nstr(1 - col(qhi), 20), nstr(1 - col(qlo), 20)))
print("  Renyi-2 (bits): p %s, q in [%s, %s]" % (nstr(-log(col(p), 2), 20), nstr(-log(col(qhi), 2), 20), nstr(-log(col(qlo), 2), 20)))
# collision sums differ: base q has a generating partition of distribution p with LARGER sum of squares
assert col(qhi) < col(p) - mpf("0.005")
print("  => over base q, the generating partition with distribution p has 1 - sum^2 smaller by > 0.005")

p3 = [mpf(1) / 3] * 3
q5 = [mpf(3) / 5] + [mpf(1) / 10] * 4
print("Pair B: H(p) = %s, H(q) = %s bits" % (nstr(H(p3), 20), nstr(H(q5), 20)))
print("  sum p^2 = %s, sum q^2 = %s" % (nstr(col(p3), 20), nstr(col(q5), 20)))
assert H(q5) > H(p3) + mpf("0.1") and col(q5) > col(p3)
print("ALL ASSERTIONS PASSED")
