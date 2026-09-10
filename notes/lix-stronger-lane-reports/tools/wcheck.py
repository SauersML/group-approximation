import sys
sys.path.insert(0, ".")
from wcoproduct import *

for p in (3, 5, 7):
    psi = build_psi(p, 2)
    M = psi[2].get((1, 1))
    print(f"p={p}: psi(e_2) block (1,1) =")
    for i in range(p):
        print("   ", M[i])
    up = all(M[u][v] % p == (1 if u < v else 0) for u in range(p) for v in range(p))
    print(f"   equals the classical sum_{{u<v}} T^u (x) T^v : {up}")
    print(f"   reduced coefficient = {sum(sum(r) for r in M) % p}  "
          f"(= C(p,2) = p(p-1)/2 = {p*(p-1)//2 % p} mod p)")
    print()

for p in (11, 13):
    n = 2 * (p - 1)
    psi = build_psi(p, n)
    cb = cbar(psi, n, p)
    C = cb.get((p - 1, p - 1), 0) % p
    odd = {(a, b): v for (a, b), v in cb.items() if a % 2 == 1}
    even = {(a, b): v for (a, b), v in cb.items() if a % 2 == 0}
    print(f"p={p}: C = cbar^({n})_({p-1},{p-1}) = {C}   "
          f"({'NONZERO' if C % p else 'ZERO'})", flush=True)
    print(f"   all a-odd reduced coefficients zero: {all(v % p == 0 for v in odd.values())}"
          f"; all a-even equal 1: {all(v % p == 1 for v in even.values())}", flush=True)
    print(f"   the two competing terms: cbar_({p},{p-2}) = {cb.get((p,p-2),0)%p}, "
          f"cbar_({p-2},{p}) = {cb.get((p-2,p),0)%p}", flush=True)
