"""The two-bank SFT on F_2 = <a, b>.

Symbol (tau, A, B): tau in {P, N}, bank values A, B in [0, K].
  a-edge s -> t (t = s*a): t.tau == P and t.A == min(s.A + 1, K), or
                            t.tau == N and s.A >= c and t.A == s.A - c.   (B free)
  b-edge s -> t (t = s*b): t.tau == N and t.B == min(s.B + 1, K), or
                            t.tau == P and s.B >= d and t.B == s.B - d.   (A free)
On an a-cycle the A-bank returns, so #P >= c #N; on a b-cycle #N >= d #P. In a finite orbit
(a finite Schreier graph) both hold globally, so c*d > 1 forces #P = #N = 0: no periodic point.

Usage: python3 bank_sft.py K c d
"""
import sys
from treesft import essential, is_si, si_defect, periodic, restrict


def build(K, c, d):
    syms = [(tau, A, B) for tau in "PN" for A in range(K + 1) for B in range(K + 1)]
    idx = {s: i for i, s in enumerate(syms)}
    n = len(syms)
    Ra = [0] * n
    Rb = [0] * n
    for s in syms:
        for t in syms:
            if (t[0] == "P" and t[1] == min(s[1] + 1, K)) or (t[0] == "N" and s[1] >= c and t[1] == s[1] - c):
                Ra[idx[s]] |= 1 << idx[t]
            if (t[0] == "N" and t[2] == min(s[2] + 1, K)) or (t[0] == "P" and s[2] >= d and t[2] == s[2] - d):
                Rb[idx[s]] |= 1 << idx[t]
    return syms, Ra, Rb


if __name__ == "__main__":
    K, c, d = (int(x) for x in sys.argv[1:4])
    syms, Ra, Rb = build(K, c, d)
    n = len(syms)
    E = essential(Ra, Rb, n)
    print(f"K={K} c={c} d={d}: {n} symbols, {bin(E).count('1')} essential")
    bad, tot = si_defect(Ra, Rb, n, E)
    print(f"SI defect: {bad} bad states of {tot} reachable non-full states -> SI = {bad == 0}")
    print("periodic point (LP):", periodic(restrict(Ra, E, n), restrict(Rb, E, n), n))
