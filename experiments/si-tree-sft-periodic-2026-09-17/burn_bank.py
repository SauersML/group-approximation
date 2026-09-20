"""Burn-bank SFT on F_2: like bank_sft.py but a bank may be burned freely, so the backward
determination that kills SI in the exact bank SFT is gone.

Symbol (tau, A, B), tau in {P, N}, A, B in [0, K].
  a-edge s -> t:  tau(t) = P  =>  A(t) <= A(s) + 1 ;   tau(t) = N  =>  A(t) <= A(s) - c.   (B free)
  b-edge s -> t:  tau(t) = N  =>  B(t) <= B(s) + 1 ;   tau(t) = P  =>  B(t) <= B(s) - d.   (A free)
On an a-cycle 0 = sum of A-increments <= #P - c #N; on a b-cycle 0 <= #N - d #P. On a finite Schreier
graph, summing over cycles gives #P >= c #N >= c d #P, so c d > 1 forces #P = #N = 0: no periodic point.

Usage: python3 burn_bank.py K c d
"""
import sys
from treesft import essential, is_si, periodic, restrict
from si_exact import hm


def build(K, c, d):
    syms = [(tau, A, B) for tau in "PN" for A in range(K + 1) for B in range(K + 1)]
    n = len(syms)
    Ra, Rb = [0] * n, [0] * n
    for i, s in enumerate(syms):
        for j, t in enumerate(syms):
            if t[1] <= s[1] + (1 if t[0] == "P" else -c):
                Ra[i] |= 1 << j
            if t[2] <= s[2] + (1 if t[0] == "N" else -d):
                Rb[i] |= 1 << j
    return syms, Ra, Rb


if __name__ == "__main__":
    K, c, d = (int(x) for x in sys.argv[1:4])
    syms, Ra, Rb = build(K, c, d)
    n = len(syms)
    E = essential(Ra, Rb, n)
    print(f"K={K} c={c} d={d}: {n} symbols, {bin(E).count('1')} essential")
    print("  path mixing:", is_si(Ra, Rb, n, E))
    print("  exact SI (half-tree mixing constant):", hm(Ra, Rb, n, E))
    print("  periodic point (LP):", periodic(restrict(Ra, E, n), restrict(Rb, E, n), n))
