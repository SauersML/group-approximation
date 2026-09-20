"""Check N/M = T_G for cyclic G = Z/n with b -> 1, a -> 2 (so c = a - b = 1 = beta).
Then T_G = <x_g | x_g = x_{g+1} x_{g+2}> is the Fibonacci group F(2,n), whose
orders for n = 2..7 are 1, 8, 5, 11, infinite, 29."""
from pushout import census_one

for n in range(2, 9):
    def shift(k):
        return tuple((i + k) % n for i in range(n))
    nG, nK, t, I = census_one(shift(2), shift(1), maxcos=300000)
    print("n=%d |G|=%d |Kbar|=%d t=%d |N/M|=%s" % (n, nG, nK, t, None if I is None else I // t), flush=True)
