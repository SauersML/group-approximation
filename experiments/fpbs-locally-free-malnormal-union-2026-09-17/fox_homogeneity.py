#!/usr/bin/env python3
"""Fox matrix of the stage inclusion of Gamma_mal and the homogeneity check.

Gamma_mal = lim (F_2 -> F_2 -> ...) along phi(a) = a, phi(b) = b a b^-2.
The stage inclusion H_n -> H_{n+1} sends the basis (a, b) of H_n to
(a, b a b^-2) in the basis (a, b) of H_{n+1}. On 1-chains with coefficients
in a right module V it acts by row vectors times the Fox matrix
J[i][j] = d(phi(s_i))/d(s_j) (left Fox derivatives).

The artifact research/artifacts/fpbs-locally-free-malnormal-union-2026-09-17.md
needs: J is lower triangular with J[0][0] = 1, and J[1][1] = 1 - T where every
group element in T has the same nonzero height under ht(a) = 1, ht(b) = 0.
This script recomputes J symbolically and checks those facts. Run:
    python3 fox_homogeneity.py
It exits nonzero if a check fails.
"""
from collections import defaultdict
import sys

# words are tuples of (letter, exponent in {+1, -1}), freely reduced


def reduce(w):
    out = []
    for x in w:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def fox(word, s):
    """Left Fox derivative d(word)/ds as dict {reduced word: integer coeff}."""
    res = defaultdict(int)
    prefix = ()
    for (l, e) in word:
        if l == s:
            if e == 1:
                res[reduce(prefix)] += 1
            else:  # d(s^-1)/ds = -s^-1
                res[reduce(prefix + ((l, -1),))] -= 1
        prefix = prefix + ((l, e),)
    return {w: c for w, c in res.items() if c != 0}


def height(w, ht):
    return sum(ht[l] * e for (l, e) in w)


def show(d):
    def wstr(w):
        return "".join(l if e == 1 else l.upper() for (l, e) in w) or "1"
    return " + ".join(f"{c}*{wstr(w)}" for w, c in sorted(d.items()))


def main():
    phi = {"a": (("a", 1),), "b": (("b", 1), ("a", 1), ("b", -1), ("b", -1))}
    gens = ["a", "b"]
    J = [[fox(phi[si], sj) for sj in gens] for si in gens]
    for i, si in enumerate(gens):
        for j, sj in enumerate(gens):
            print(f"J[{si},{sj}] = {show(J[i][j]) or '0'}")
    ok = True
    ok &= J[0][0] == {(): 1}
    ok &= J[0][1] == {}
    x = dict(J[1][1])
    ok &= x.get((), 0) == 1
    x.pop((), None)
    ht = {"a": 1, "b": 0}
    heights = {height(w, ht) for w in x}
    print("non-identity terms of J[b,b]:", show(x), "heights:", sorted(heights))
    ok &= len(heights) == 1 and 0 not in heights
    # also check the Fox identity  phi(b) - 1 = sum_j J[b,j] (s_j - 1)
    # by comparing supports in the group ring
    lhs = defaultdict(int)
    lhs[reduce(phi["b"])] += 1
    lhs[()] -= 1
    rhs = defaultdict(int)
    for j, sj in enumerate(gens):
        for w, c in J[1][j].items():
            rhs[reduce(w + ((sj, 1),))] += c
            rhs[w] -= c
    lhs = {w: c for w, c in lhs.items() if c}
    rhs = {w: c for w, c in rhs.items() if c}
    print("Fox identity holds:", lhs == rhs)
    ok &= lhs == rhs
    print("ALL CHECKS PASS" if ok else "CHECK FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
