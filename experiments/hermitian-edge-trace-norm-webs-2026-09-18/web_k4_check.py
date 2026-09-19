# Exact check for the webs C_n^4 (m = 5) by clique windows with the certified c_5 >= 7.0857.
# Windows prove the rank inequality iff n c_5 >= sqrt3 (4n + r), r = n mod 5, i.e. (n c_5)^2 >= 3 (4n + r)^2.
from fractions import Fraction as Fr
c5 = Fr(70857, 10000); sHi = Fr(17320509, 10**7); assert sHi**2 > 3
eps_lo = c5 - 4 * sHi
N0 = int(4 * sHi / eps_lo) + 1          # for n >= N0: n eps_5 >= 4 sqrt3 >= sqrt3 r
bad = [n for n in range(10, N0 + 1) if not (n * c5) ** 2 >= 3 * (4 * n + n % 5) ** 2]
print("c_5 >= 7.0857: eps_5 >= %.6f, N0 = %d" % (float(eps_lo), N0))
print("k = 4, n >= 10: windows fail exactly for n in", bad)
