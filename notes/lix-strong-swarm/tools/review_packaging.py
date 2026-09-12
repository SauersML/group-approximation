# lx-review round 3: normalisation of the OddPTotal packaging (de17c2bb1) against Steenrod-Epstein.
# Classical: on H^q, D_{(q-2i)(p-1)} = nu(q)^{-1} (-1)^i P^i, nu(q) = (-1)^{m q(q-1)/2} (m!)^q, m = (p-1)/2.
# Packaging: totalP s on degree a = 2k is mu^{-(k-s)} * [D_{(2k-2s)(p-1)}], with mu = [D_{2(p-1)}] on H^2(CP^M).
# Predicates, mod p, for odd primes p <= 101:
#  (a) mu := nu(2)^{-1} * (-1)^0 = -1
#  (b) mu^{-(k-s)} * nu(2k)^{-1} * (-1)^s == 1  for all k <= 40, s <= k   (totalP s = P^s)
#  (c) zero_cp: totalP 0 on degree 2 = mu^{-1} * mu = 1; degree_two: totalP 1 on degree 2 = [D_0] = h^p, kappa = 1
#  (d) GoodDeg bound: a + 2s(p-1) <= p*a  <=>  s <= a/2, for even a <= 80, s <= 80
#  (e) Cartan exponents: (a/2 - j) + (b/2 - (i-j)) == (a+b)/2 - i whenever j <= a/2, i-j <= b/2
from math import factorial
def primes(N):
    return [p for p in range(3, N) if all(p % d for d in range(2, int(p**0.5)+1))]
checks = fails = 0
def chk(b):
    global checks, fails
    checks += 1; fails += (not b)
for p in primes(102):
    m = (p-1)//2; mf = factorial(m) % p
    nu = lambda q: ((-1)**(m*q*(q-1)//2) * pow(mf, q, p)) % p
    inv = lambda x: pow(x % p, p-2, p)
    mu = inv(nu(2)) % p
    chk(mu == p-1)
    for k in range(41):
        for s in range(k+1):
            chk((pow(inv(mu), k-s, p) * inv(nu(2*k)) * (-1)**s) % p == 1)
    chk((inv(mu)*mu) % p == 1)
    for a in range(0, 81, 2):
        for s in range(81):
            chk((a + 2*s*(p-1) <= p*a) == (s <= a//2))
for a in range(0, 41, 2):
    for b in range(0, 41, 2):
        for i in range(41):
            for j in range(i+1):
                if j <= a//2 and i-j <= b//2:
                    chk((a//2 - j) + (b//2 - (i-j)) == (a+b)//2 - i)
print("primes:", len(primes(102)), "checks:", checks, "failures:", fails)
