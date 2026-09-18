#!/usr/bin/env python3
"""Checks for fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility.

Part 1. On T_k = Cay((Z/2)^{*k}), with an end xi and height h(e,v) (steps
        toward xi minus steps away), check that
          g(v) = (k-1)^{h(e,v)/2} satisfies A g = 2 sqrt(k-1) g,
          sum_{|v|=n} g(v) = P_n(2 sqrt(k-1)),
          P_n(2 sqrt(k-1)) = (k-1)^{n/2} (2 + (n-1)(k-2)/(k-1))  (n >= 1),
        where P_0 = 1, P_1 = x, P_2 = x^2 - k, P_{n+1} = x P_n - (k-1) P_{n-1}
        are the sphere polynomials, A_n = P_n(A).
Part 2. Degenerate calibration (H a point): sigma(v) = p^{|v|}, so
        chi_{p,1/2} = sum_n p^n P_n(rho), finite iff p < (k-1)^{-1/2},
        which is p_(2->2)(T_k) and Hutchcroft's p_t for the end-fixing group.
Part 3. Mean-field constants for T_4 x T_4 (8 uniform steps), recorded in the
        Attempts of fpbs-tree-product-fibre-square-root-law-below-relative-threshold.
Exact rational/float arithmetic only; no randomness.
"""
import math
from itertools import product


def reduced_words(k, L):
    words = [()]
    frontier = [()]
    for _ in range(L):
        nxt = []
        for w in frontier:
            for s in range(k):
                if w and w[-1] == s:
                    continue
                nxt.append(w + (s,))
        words.extend(nxt)
        frontier = nxt
    return words


def dist(u, v):
    m = 0
    while m < min(len(u), len(v)) and u[m] == v[m]:
        m += 1
    return len(u) + len(v) - 2 * m


def height(v, xi):
    # Busemann height toward the end xi: lim_L d(e, xi_L) - d(v, xi_L).
    L = len(xi)
    return L - dist(v, xi)


def P(n, x, k):
    if n == 0:
        return 1.0
    a, b = 1.0, x
    for m in range(1, n):
        c = (k if m == 1 else (k - 1))
        a, b = b, x * b - c * a
    return b


def part1():
    ok = True
    for k in (3, 4, 5, 6):
        R = 7
        xi = tuple(i % 2 for i in range(40))  # the ray s0 s1 s0 s1 ...
        W = reduced_words(k, R)
        rho = 2 * math.sqrt(k - 1)
        g = {w: (k - 1) ** (height(w, xi) / 2) for w in W}
        # eigen-equation on the interior of the ball
        worst = 0.0
        for w in W:
            if len(w) >= R:
                continue
            nb = [w[:-1]] if w else []
            nb += [w + (s,) for s in range(k) if not (w and w[-1] == s)]
            Ag = sum(g[x] for x in nb)
            worst = max(worst, abs(Ag - rho * g[w]) / g[w])
        line = [f"k={k}: max rel err of Ag=rho g on B_{R-1}: {worst:.2e}"]
        ok &= worst < 1e-12
        for n in range(0, R + 1):
            s = sum(g[w] for w in W if len(w) == n)
            pn = P(n, rho, k)
            cf = 1.0 if n == 0 else (k - 1) ** (n / 2) * (2 + (n - 1) * (k - 2) / (k - 1))
            good = abs(s - pn) < 1e-9 * max(1, pn) and abs(cf - pn) < 1e-9 * max(1, pn)
            ok &= good
            line.append(f"  n={n}: sum_S_n g={s:.6f} P_n(rho)={pn:.6f} closed={cf:.6f} {'OK' if good else 'FAIL'}")
        print("\n".join(line))
    return ok


def part2():
    ok = True
    for k in (3, 4, 5):
        pt = (k - 1) ** -0.5
        rho = 2 * math.sqrt(k - 1)
        out = [f"k={k}: predicted p_t = (k-1)^(-1/2) = {pt:.6f}"]
        for p in (0.9 * pt, 0.99 * pt, pt, 1.01 * pt):
            # p^n P_n(rho) = (p sqrt(k-1))^n (2 + (n-1)(k-2)/(k-1)) for n >= 1 (Part 1);
            # use this closed form to avoid overflow at large n.
            q = p * math.sqrt(k - 1)
            terms = [1.0] + [q ** n * (2 + (n - 1) * (k - 2) / (k - 1)) for n in range(1, 4000)]
            tail = terms[-1]
            partial = sum(terms)
            out.append(f"  p={p:.6f}: partial sum (n<4000)={partial:.4e}, last term={tail:.4e}")
            if p < pt:
                ok &= tail < 1e-1
            else:
                ok &= tail > 1.0
        print("\n".join(out))
    return ok


def part3():
    k = 4
    rho_tree = 2 * math.sqrt(k - 1) / k  # SRW spectral radius of T_4
    rho_lazy = 0.5 + 0.5 * rho_tree       # projected walk of the 8-step product walk
    rho_prod = 0.5 * rho_tree + 0.5 * rho_tree
    print(f"T_4: SRW spectral radius {rho_tree:.5f}")
    print(f"lazy projected tree walk spectral radius 1/2 + sqrt3/4 = {rho_lazy:.5f}")
    print(f"fibre-occupation threshold m_* = 1/rho_lazy = {1/rho_lazy:.5f}")
    print(f"product walk spectral radius = {rho_prod:.5f}; point threshold 1/rho = {1/rho_prod:.5f} (= 2/sqrt3 = {2/math.sqrt(3):.5f})")
    return abs(1 / rho_lazy - 1.07180) < 1e-4 and abs(1 / rho_prod - 2 / math.sqrt(3)) < 1e-12


if __name__ == "__main__":
    r1 = part1()
    print()
    r2 = part2()
    print()
    r3 = part3()
    print()
    print("ALL OK" if (r1 and r2 and r3) else "SOME CHECK FAILED")
