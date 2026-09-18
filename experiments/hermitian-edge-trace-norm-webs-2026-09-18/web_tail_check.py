# Exact check: for every m >= 11,  eps_m (3m-1) > sqrt3 (m-1),  where
#   eps_m = L(m) - sqrt3 (m-1),  L(m) = 2 (c00 m^2 - F1 m)/(m-1)   (large-m clique bound, m >= 6).
# Multiply by (m-1) > 0:  p(m) = (3m-1) (2 c00 m^2 - 2 F1 m - s (m-1)^2) - s (m-1)^2 > 0,  s = sqrt3.
# Write p(11+x) = sum_i (a_i + b_i s) x^i with rationals a_i, b_i and bound each coefficient below
# using 17320508/10^7 < s < 17320509/10^7 (choosing the endpoint by the sign of b_i).
from fractions import Fraction as Fr
c00 = Fr(4512199, 5000000); F1 = Fr(8906037, 5000000)
sLo, sHi = Fr(17320508, 10**7), Fr(17320509, 10**7)
assert sLo**2 < 3 < sHi**2
# polynomials in x as dict power -> (a, b) meaning a + b*s
def mul(P, Q):
    R = {}
    for i, (a1, b1) in P.items():
        for j, (a2, b2) in Q.items():
            a, b = R.get(i + j, (Fr(0), Fr(0)))
            # (a1 + b1 s)(a2 + b2 s) = a1a2 + 3 b1b2 + (a1b2 + a2b1) s
            R[i + j] = (a + a1 * a2 + 3 * b1 * b2, b + a1 * b2 + a2 * b1)
    return R
def add(P, Q, c=1):
    R = dict(P)
    for i, (a, b) in Q.items():
        a0, b0 = R.get(i, (Fr(0), Fr(0)))
        R[i] = (a0 + c * a, b0 + c * b)
    return R
m = {0: (Fr(11), Fr(0)), 1: (Fr(1), Fr(0))}          # m = 11 + x
one = {0: (Fr(1), Fr(0))}
s = {0: (Fr(0), Fr(1))}
mm1 = add(m, one, -1)
A = add(add(mul({0: (2 * c00, Fr(0))}, mul(m, m)), mul({0: (2 * F1, Fr(0))}, m), -1), mul(s, mul(mm1, mm1)), -1)
p = add(mul(add(mul({0: (Fr(3), Fr(0))}, m), one, -1), A), mul(s, mul(mm1, mm1)), -1)
ok = True
for i in sorted(p):
    a, b = p[i]
    lb = a + b * (sLo if b > 0 else sHi)
    print("x^%d: lower bound %.6f" % (i, float(lb)))
    ok &= lb > 0
print("all coefficients of p(11+x) positive:", ok)
# direct exact check m = 6..40 of eps_m (3m-1) > s (m-1), i.e. p(m) > 0, with s bracketed
def pval(mv, sv):
    return (3 * mv - 1) * (2 * c00 * mv * mv - 2 * F1 * mv - sv * (mv - 1) ** 2) - sv * (mv - 1) ** 2
bad = [mv for mv in range(6, 41) if not pval(Fr(mv), sHi) > 0]   # p decreasing in s
print("m in 6..40 failing the sufficient condition:", bad)

# Part 2. Exact exception lists for 3 <= k <= 9 (m = k + 1), n >= 2k + 2.
# Clique windows prove (**) at the rank inequality of C_n^k iff  n c_m >= sqrt3 (n (m-1) + r),  r = n mod m,
# i.e. (n c_m)^2 >= 3 (n (m-1) + r)^2  (both sides positive). Certified rational lower bounds c_m:
#   m = 4: c_4 >= 5.3887 (graphbb K4, by-size route);  m >= 6: L(m) = 2 (c00 m^2 - F1 m)/(m-1) (large-m Steps 2-4).
#   m = 5: only c_5 >= 4 sqrt3 is certified, which proves nothing for r > 0; k = 4 is skipped.
def Lm(mv):
    return 2 * (c00 * mv * mv - F1 * mv) / (mv - 1)
def cert(mv):
    return Fr(53887, 10000) if mv == 4 else Lm(Fr(mv))
def windows_ok(n, mv):
    r = n % mv
    return (n * cert(mv)) ** 2 >= 3 * (n * (mv - 1) + r) ** 2
print()
for k in [3] + list(range(5, 30)):
    mv = k + 1
    # beyond N0 the condition holds for all n: it suffices that n eps >= sqrt3 (m-1), eps = c_m - sqrt3 (m-1)
    eps_lo = cert(mv) - sHi * (mv - 1)
    if eps_lo <= 0:
        print("k=%d: eps_m <= 0, no window proof" % k); continue
    N0 = int(sHi * (mv - 1) / eps_lo) + 1
    bad = [n for n in range(2 * k + 2, max(N0, 2 * k + 2) + 1) if not windows_ok(n, mv)]
    print("k=%d m=%d eps_m >= %.5f, all n >= %d pass trivially; exceptions n >= 2k+2: %s"
          % (k, mv, float(eps_lo), N0, bad if len(bad) <= 70 else "%d, max %d" % (len(bad), max(bad))))
