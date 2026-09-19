# Exact check for research/hermitian-edge-trace-norm-web-rank-k3-p6cube-windows.md.
# Windows of 6 consecutive vertices of C_n^3 (n >= 9) induce P_6^3 and cover each vertex 6 times,
# so ||C||_1 >= (n/6) c(P_6^3).  With c(P_6^3) >= b = 8.3139 the rank inequality
# ||C||_1 >= sqrt3 (n - floor(n/4)) follows when (n b)^2 >= 108 (n - floor(n/4))^2 (exact integers).
from fractions import Fraction as Fr
b = Fr(83139, 10000)
bad = [n for n in range(9, 400) if (n * b) ** 2 < 108 * (n - n // 4) ** 2]
print("b = 8.3139; n in [9, 400) where the windows fail:", bad)
# Tail: n - floor(n/4) <= (3n + 3)/4, so it suffices that (n b / 6)^2 >= 3 ((3n + 3)/4)^2,
# i.e. n (b/6) - sqrt3 (3/4)(n + 1) >= 0; with sqrt3 < s = 17321/10000 this holds for n >= N0.
s = Fr(17321, 10000); assert s * s > 3
g = b / 6 - s * Fr(3, 4); assert g > 0
N0 = -(-(s * Fr(3, 4)) // g)
print("gap b/6 - (3/4) sqrt3 >= %s > 0; tail bound holds for every n >= %d" % (float(g), N0))
assert N0 <= 400 and all(n * g >= s * Fr(3, 4) for n in range(N0, N0 + 5))
print("so for k = 3 the windows prove the rank inequality for every n >= 9 except", bad)
