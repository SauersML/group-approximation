#!/usr/bin/env python3
"""Exact Br/TJT on hairpin and straight paths for the column environment.

Environment Z (on Z^2): every vertical edge, plus the horizontal edge
h(j,y) = ((j-1,y),(j,y)) iff max(zeta_{j,y-1}, zeta_{j,y}, zeta_{j,y+1}) = 1,
zeta i.i.d. Bernoulli(q).  Connected, Z^2-invariant, monotone, range 1.

Hairpin H_m: (0,0)..(m,0), (m,1), (m,2), (m-1,2)..(0,2); n = 2m+2 edges.
Straight path S_n: (0,0)..(n,0).

Everything is computed by brute force from the formulas of
fpbs-percolation-spine-path-bridge-ratio-criterion, Theorem 1(a):
  t(i,j) = E r^{N(i,j]},  T = t(0,n),
  TJT = sum_k [t(0,k-1) t(k,n) + t(0,k) t(k-1,n)],
  Br  = E[G r^{N-1}],  G = number of interior gaps,
using the exact joint law of the path-edge indicators (a product over columns),
and compared with the closed forms of the proof.
"""
import itertools, math, sys

def column_law(q):
    """Joint law of (a, b) = coverage of h(j,0), h(j,2): shares zeta_{j,1}."""
    law = {}
    for z in itertools.product((0, 1), repeat=5):       # zeta_{j,-1..3}
        w = 1.0
        for s in z:
            w *= q if s else 1 - q
        a = max(z[0], z[1], z[2]); b = max(z[2], z[3], z[4])
        law[(a, b)] = law.get((a, b), 0.0) + w
    return law

def hairpin_exact(q, r, m):
    """Exact t, TJT, Br on H_m by transfer over columns (no enumeration of 2^n)."""
    law = column_law(q)
    n = 2 * m + 2
    # path order: e_1..e_m = a_1..a_m, e_{m+1}, e_{m+2} turn (always in Z),
    # e_{m+3}..e_n = b_m..b_1.  col(k), side(k):
    def col(k):
        if k <= m: return k, 'a'
        if k <= m + 2: return None, 't'
        return n - k + 1, 'b'
    def t(i, j):                      # E r^{N(i,j]}
        cols = {}
        for k in range(i + 1, j + 1):
            c, s = col(k)
            if c is not None:
                cols.setdefault(c, set()).add(s)
        val = 1.0
        for c, S in cols.items():
            e = 0.0
            for (a, b), w in law.items():
                miss = (('a' in S) and a == 0) + (('b' in S) and b == 0)
                e += w * r ** miss
            val *= e
        return val
    T = t(0, n)
    TJT = sum(t(0, k - 1) * t(k, n) + t(0, k) * t(k - 1, n) for k in range(1, n + 1))
    # Br = E[G r^{N-1}] = (T/r) E*[G]; under the r^N tilt columns stay independent.
    Zc = sum(w * r ** ((a == 0) + (b == 0)) for (a, b), w in law.items())
    alpha = sum(w * r ** ((a == 0) + (b == 0)) for (a, b), w in law.items() if a == 0) / Zc
    # a_j is an interior gap iff a_j = 0 and some a_i = 1 (i < j): the turn is covered.
    EG = 2 * sum(alpha * (1 - alpha ** (j - 1)) for j in range(1, m + 1))
    Br = T / r * EG
    return n, T, TJT, Br, alpha, law

def straight_exact(q, r, n):
    law = column_law(q)
    lam = sum(w * (r if a == 0 else 1.0) for (a, b), w in law.items())
    t = lambda i, j: lam ** (j - i)
    T = t(0, n)
    TJT = sum(t(0, k - 1) * t(k, n) + t(0, k) * t(k - 1, n) for k in range(1, n + 1))
    al = sum(w for (a, b), w in law.items() if a == 0) * r / lam   # tilted P*(uncovered)
    # interior gap: e_k uncovered, some covered edge on each side (i.i.d. tilted edges)
    EG = sum(al * (1 - al ** (k - 1)) * (1 - al ** (n - k)) for k in range(1, n + 1))
    Br = T / r * EG
    return n, T, TJT, Br

def brute_hairpin(q, r, m):
    """Enumerate all 2^(2m) coverage patterns: independent check of hairpin_exact."""
    law = column_law(q)
    n = 2 * m + 2
    cols = list(itertools.product(law.keys(), repeat=m))
    def cov(pat):   # coverage vector in path order
        a = [pat[j][0] for j in range(m)]; b = [pat[j][1] for j in range(m)]
        return a + [1, 1] + b[::-1]
    tt = {}
    Br = 0.0
    for pat in cols:
        w = 1.0
        for ab in pat: w *= law[ab]
        c = cov(pat)
        N = [0]
        for x in c: N.append(N[-1] + (1 - x))
        for i in range(n + 1):
            for j in range(i, n + 1):
                tt[(i, j)] = tt.get((i, j), 0.0) + w * r ** (N[j] - N[i])
        G = 0
        for k in range(n):
            if c[k] == 0 and any(c[:k]) and any(c[k + 1:]): G += 1
        Br += w * G * r ** (N[n] - 1)
    T = tt[(0, n)]
    TJT = sum(tt[(0, k - 1)] * tt[(k, n)] + tt[(0, k)] * tt[(k - 1, n)] for k in range(1, n + 1))
    return T, TJT, Br

def closed_form(q, r, m):
    u = 1 - q
    lam = 1 - u ** 3 + r * u ** 3
    rho = 1 + (1 - r) ** 2 * u ** 5 * (1 - u) / lam ** 2
    nD = 2 * sum(rho ** (-j) / lam + lam * rho ** (1 - j) for j in range(1, m + 1)) + 4 * rho ** (-m)
    A = 2 * (1 / lam + lam * rho) / (rho - 1)
    return lam, rho, nD, A

if __name__ == "__main__":
    print("# brute-force check of the transfer formula (small m)")
    for q, r, m in [(0.3, 0.5, 3), (0.5, 0.2, 4), (0.2, 0.8, 4)]:
        n, T, TJT, Br, al, _ = hairpin_exact(q, r, m)
        T2, TJT2, Br2 = brute_hairpin(q, r, m)
        lam, rho, nD, A = closed_form(q, r, m)
        print(f"q={q} r={r} m={m}: T {T:.12g} vs {T2:.12g}; TJT {TJT:.12g} vs {TJT2:.12g}; "
              f"Br {Br:.12g} vs {Br2:.12g}; nD_n {TJT / T:.12g} vs closed {nD:.12g}")
    print()
    print("# hairpin H_m vs straight path S_n, same environment, n = 2m+2")
    print("# q    r     n    nD_n(H)   A=lim nD_n  Br/TJT(H)  slope_pred*n   Br/TJT(S)  D_n(S)")
    for q in (0.1, 0.3, 0.5):
        for r in (0.1, 0.3, 0.6, 0.9):
            lam, rho, _, A = closed_form(q, r, 1)
            for m in (4, 9, 19, 49, 99, 199):
                n, T, TJT, Br, al, _ = hairpin_exact(q, r, m)
                nS, TS, TJTS, BrS = straight_exact(q, r, n)
                print(f"{q:<4} {r:<4} {n:6d} {TJT / T:10.5f} {A:10.5f} {Br / TJT:10.5f} "
                      f"{al * n / (r * A):11.5f} {BrS / TJTS:10.5f} {TJTS / (nS * TS):8.5f}")
            for m in (999, 9999, 99999):     # closed forms (Theorem 2 of the proof)
                lam, rho, nD, A = closed_form(q, r, m)
                n = 2 * m + 2
                law = column_law(q)
                Zc = sum(w * r ** ((a == 0) + (b == 0)) for (a, b), w in law.items())
                al = sum(w * r ** ((a == 0) + (b == 0)) for (a, b), w in law.items() if a == 0) / Zc
                EG = 2 * (m * al - al * (1 - al ** m) / (1 - al))
                print(f"{q:<4} {r:<4} {n:6d} {nD:10.5f} {A:10.5f} {EG / (r * nD):10.5f} "
                      f"{al * n / (r * A):11.5f}   (closed form)")
