# Exact threshold checks for Cay(F_k x Z, standard) = T_{2k} x Z, k >= 2.
# GW side: fibre-interval Galton-Watson process, mean m_k(p) = (2k-1)(1 - (1-p) phi^2),
#          phi = (1-p)/(1-p+p^2).  m_k(p1) > 1  =>  theta(p1) > 0.
# l2 side: k = 2 uses the ell=4 Busemann Schur certificate (certschur.py, lambda <= 829/200);
#          k >= 3 uses ||T_p|| <= sum p^n ||A||^n, ||A|| = 2 + 2 sqrt(2k-1).
import random
from fractions import Fraction as Fr

def m(p, k):
    phi = (1 - p) / (1 - p + p * p)
    return (2 * k - 1) * (1 - (1 - p) * phi * phi)

def p_norm_below_one(p, k):
    # exact test of p (2 + 2 sqrt(2k-1)) < 1  <=>  (1/p - 2)/2 > sqrt(2k-1)
    r = (1 / p - 2) / 2
    return r > 0 and r * r > 2 * k - 1

ok = True
# k = 2
p1, p2, lam = Fr(236, 1000), Fr(241, 1000), Fr(829, 200)
c1, c2 = m(p1, 2) > 1, p2 * lam < 1
print("k=2  m(236/1000) =", float(m(p1, 2)), c1, "| (241/1000)(829/200) =", float(p2 * lam), c2)
ok &= c1 and c2 and p1 < p2
# k = 3, 4 by adjacency norm
for k, a, b in ((3, Fr(1544, 10000), Fr(1545, 10000)), (4, Fr(12, 100), Fr(13, 100))):
    c1, c2 = m(a, k) > 1, p_norm_below_one(b, k)
    print("k=%d  m(%s) =" % (k, a), float(m(a, k)), c1, "| %s ||A|| < 1:" % b, c2)
    ok &= c1 and c2 and a < b
# k >= 5: m_k(p) >= (2k-1) p since phi <= 1; 1/(2k-1) < 1/(2+2sqrt(2k-1)) iff 2k-1 > 4+2sqrt3
for k in range(5, 60):
    n = 2 * k - 1
    a = Fr(1, n) * Fr(1001, 1000)
    # choose b strictly between a and 1/||A||: test midpoint of a and 1/(2+2 sqrt n) via rational under-approx
    b = a * Fr(1001, 1000)
    c = (n * a > 1) and (m(a, k) >= n * a) and p_norm_below_one(b, k) and a < b
    ok &= c
print("k=5..59 elementary checks:", ok)
print("analytic k>=5 condition 2k-1 > 4+2sqrt3 (=7.4641): k=5 gives 9")
# sanity: simulate the fibre-interval offspring mean for k = 2 at p = 0.236
random.seed(1)
p = 0.236; T = 200000; tot = 0
for _ in range(T):
    L = 1
    while random.random() < p: L += 1
    while random.random() < p: L += 1
    for t in range(3):
        tot += any(random.random() < p for _ in range(L))
print("simulated mean k=2 p=0.236:", tot / T, "formula:", float(m(Fr(236, 1000), 2)))
print("ALL OK" if ok else "FAIL")
