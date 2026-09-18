# Exact check of the tail n = 2k+1 >= 15 of the odd-antihole facet inequality.
# Clique averaging: ||C||_1 >= (n/k) c_k, where c_k is any lower bound for ||.||_1 over admissible
# matrices on K_k.  The landed LP (research/hermitian-edge-trace-norm-clique-inequality-large-m-proof.md,
# Steps 2-4, valid for every m) gives c_m >= 2 (c00 m^2 - m F1)/(m-1).  Needed: (n/k) c_k >= sqrt3 (n-2),
# i.e. (dividing by 2k/(k-1) > 0)
#   p(k) = 2 (c00 k - F1)(2k+1) - sqrt3 (2k-1)(k-1) >= 0.
# The sqrt3 coefficient -(2k-1)(k-1) is < 0 for k >= 2, so replacing sqrt3 by an upper bound s gives a lower
# bound for p.  p_s is a quadratic; we check p_s(7) > 0, leading coefficient > 0, vertex <= 7 (exact).
from fractions import Fraction as Fr
c00=Fr(4512199,5000000); F1=Fr(8906037,5000000)
s=Fr(17320509,10**7); assert s*s>3
a=4*c00-2*s; b=2*c00-4*F1+3*s; c=-(2*F1+s)
p=lambda k: a*k*k+b*k+c
assert a>0 and -b/(2*a)<=7 and p(7)>0
print("a=%s b=%s c=%s  p_s(6)=%.5f  p_s(7)=%.5f  vertex %.4f"%(float(a),float(b),float(c),float(p(6)),float(p(7)),float(-b/(2*a))))
print("RESULT: p(k) > 0 for all integers k >= 7, i.e. the facet inequality holds on C_n-bar for all odd n >= 15")
