# lx-review: consistency of the programme's reduced-power normalisation constants with the classical
# Steenrod-Epstein nu(q) = (-1)^{m q(q-1)/2} (m!)^q mod p, m = (p-1)/2, and kappa_top(q,q') = (-1)^{m q q'}.
# Predicates (all mod p, exact integer arithmetic reduced mod p):
#  (a) c_1 = m!                           equals nu(1)
#  (b) c_2 = -1                           equals nu(2)            (Wilson: (m!)^2 = (-1)^{m+1})
#  (c) c_{2k} = (-1)^k                    equals nu(2k)
#  (d) nu(q+q') = kappa_top(q,q') nu(q) nu(q')   for all q,q' <= 12
#  (e) nu(q) is a unit mod p for every q <= 40
from math import factorial
def primes(N):
    return [p for p in range(3, N) if all(p % d for d in range(2, int(p**0.5)+1))]
fails = 0; checks = 0
for p in primes(60):
    m = (p-1)//2; mf = factorial(m) % p
    nu = lambda q: ((-1)**(m*q*(q-1)//2) * pow(mf, q, p)) % p
    kap = lambda q, r: ((-1)**(m*q*r)) % p
    tests = [(nu(1) == mf), (nu(2) == (-1) % p)]
    tests += [nu(2*k) == ((-1)**k) % p for k in range(0, 20)]
    tests += [nu(q+r) == (kap(q, r)*nu(q)*nu(r)) % p for q in range(13) for r in range(13)]
    tests += [nu(q) != 0 for q in range(41)]
    checks += len(tests); fails += tests.count(False)
    if not all(tests): print("FAIL at p =", p)
print("primes 3..59:", len(primes(60)), "checks:", checks, "failures:", fails)
