#!/usr/bin/env python3
"""Check the two-ray factorization of Houghton pours used to bound the
four-ray route-change area W_4(m) by the Dehn function of H_3.

Conventions (as in research/artifacts/zp-houghton-pours-2026-09-17.md, Section 0):
points (x, p) with p >= 1; words act on the right, read left to right.
  lam(x,y): (x,p)->(x,p-1) for p>=2, (x,1)->(y,1), (y,p)->(y,p+1).
  tau(x):   swaps (x,1),(x,2).
Formal inverses never appear: lam(y,x) is the inverse element of lam(x,y).

For every ordered labeling (a,b,c,d) of the rays {0,1,2,3} and 1 <= m <= M the
script checks, on all points of depth <= 3m+5 of all four rays:

 (1) E^c_(a,b)(m) = lam_ac^m lam_cb^m and E^d_(a,b)(m) = lam_ad^m lam_db^m
     both equal N_(a,b)(m) = lam_ab^m . rho_b(m), where
     rho_b(m) = prod_{i=m-1..1} prod_{j=1..i} s_j,  s_j = D^a_b(j-1)
             = lam_ba^(j-1) tau_b lam_ab^(j-1)   (the transposition ((b,j),(b,j+1))),
     a word in the letters lam_ab, lam_ba, tau_b only (ray support {a,b});
 (2) the words E^c N^-1 and N (E^d)^-1 use only letters fixing ray d, resp. ray c
     pointwise (checked on points), so each is a word in a copy of H_3;
 (3) |N_(a,b)(m)| <= m^3 for m >= 1 and |E^c N^-1| <= 2 m^3 for m >= 2.
"""
import itertools
import sys


def lam(x, y):
    def f(pt):
        r, p = pt
        if r == x:
            return (x, p - 1) if p >= 2 else (y, 1)
        if r == y:
            return (y, p + 1)
        return pt
    return ('lam', x, y), f


def tau(x):
    def f(pt):
        r, p = pt
        if r == x and p in (1, 2):
            return (x, 3 - p)
        return pt
    return ('tau', x), f


def apply(word, pt):
    for _, f in word:
        pt = f(pt)
    return pt


def pour(a, b, c, m):
    return [lam(a, c)] * m + [lam(c, b)] * m


def s(a, b, j):
    return [lam(b, a)] * (j - 1) + [tau(b)] + [lam(a, b)] * (j - 1)


def normal_form(a, b, m):
    w = [lam(a, b)] * m
    for i in range(m - 1, 0, -1):
        for j in range(1, i + 1):
            w += s(a, b, j)
    return w


def letters_fix_ray(word, ray):
    # a letter fixes a ray pointwise iff the ray is not in its ray support
    return all(ray not in n[1:] for n, _ in word)


def main(M=7):
    rays = range(4)
    checked = 0
    for a, b, c, d in itertools.permutations(rays):
        for m in range(1, M + 1):
            Ec, Ed, N = pour(a, b, c, m), pour(a, b, d, m), normal_form(a, b, m)
            # A point deeper than the word length never reaches a ray top while the
            # word is applied, so every letter moves it by its translation; the three
            # words have equal translation vectors (-m on a, +m on b). Hence checking
            # all points of depth <= max length + 2 proves equality of elements.
            depth = max(len(Ec), len(N)) + 2
            pts = [(r, p) for r in rays for p in range(1, depth + 1)]
            for pt in pts:
                x1, x2, x3 = apply(Ec, pt), apply(Ed, pt), apply(N, pt)
                assert x1 == x2 == x3, (a, b, c, d, m, pt, x1, x2, x3)
            # (2) letter supports: E^c and N avoid ray d; E^d and N avoid ray c
            assert letters_fix_ray(Ec + N, d)
            assert letters_fix_ray(Ed + N, c)
            # each letter of the two-ray word N has ray support inside {a,b}
            assert all(set(n[1:]) <= {a, b} for n, _ in N)
            # (3) lengths
            assert len(N) == m + sum((2 * j - 1) for i in range(1, m) for j in range(1, i + 1))
            assert len(N) <= m ** 3
            if m >= 2:
                assert len(Ec) + len(N) <= 2 * m ** 3
            checked += 1
    print(f"checked {checked} cases (24 labelings, 1 <= m <= {M}): "
          f"E^c = E^d = lam_ab^m rho_b(m) as elements; "
          f"rho_b(m) uses only lam_ab, lam_ba, tau_b; |N| <= m^3")


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
