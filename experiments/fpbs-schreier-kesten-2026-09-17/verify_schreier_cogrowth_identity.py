#!/usr/bin/env python3
"""Consistency check for fpbs-tree-subgroup-relative-gap-iff-not-co-amenable.

For a subgroup H of F_2 (q = 3) given by a folded Stallings core graph, compare
coefficientwise, for n <= NMAX:

  f_n(H) = #{reduced words of length n lying in H}
  [s^n] phi(s) * sum_m W_m(H) z(s)^m,   W_m(H) = #{all words of length m with reduced form in H}

where z(s) = s/(1+q s^2), phi(s) = (1-s^2)/(1+q s^2).  W_m(H) = (q+1)^m p_m is the
return count of simple random walk on the Schreier graph H\\F_2.  The identity uses
only the word recursion A_n A = A_(n+1) + q A_(n-1), so it holds for every
subgroup, normal or not.  Calibration only, not part of any proof.
"""
from itertools import product
from math import comb

NMAX = 9
Q = 3
LETTERS = ["a", "A", "b", "B"]  # A = a^-1, B = b^-1
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def reduce(word):
    out = []
    for x in word:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return out


def make_member(core_edges):
    """core_edges: dict (vertex, letter in {a,b}) -> vertex, a folded partial action."""
    trans = {}
    for (v, x), w in core_edges.items():
        trans[(v, x)] = w
        trans[(w, INV[x])] = v

    def member(red):
        v = 0
        for x in red:
            if (v, x) not in trans:
                return False
            v = trans[(v, x)]
        return v == 0

    return member


def counts(member):
    f = [0] * (NMAX + 1)
    W = [0] * (NMAX + 1)
    for m in range(NMAX + 1):
        for w in product(LETTERS, repeat=m):
            r = reduce(w)
            if member(r):
                W[m] += 1
                if len(r) == m:
                    f[m] += 1
    return f, W


def rhs(W):
    coeff = [0] * (NMAX + 1)
    for m in range(NMAX + 1):
        # s^m (1 - s^2) (1 + q s^2)^(-(m+1))
        for k in range(0, NMAX + 1):
            e = m + 2 * k
            if e > NMAX:
                break
            c = comb(m + k, k) * (-Q) ** k * W[m]
            coeff[e] += c
            if e + 2 <= NMAX:
                coeff[e + 2] -= c
    return coeff


def perm_core(pa, pb):
    edges = {}
    for i, j in enumerate(pa):
        edges[(i, "a")] = j
    for i, j in enumerate(pb):
        edges[(i, "b")] = j
    return edges


EXAMPLES = {
    # infinite index, not co-amenable (Schreier graph has infinitely many ends)
    "<a>": {(0, "a"): 0},
    # infinite index, non-normal, not co-amenable
    "<a, b a b^-1>": {(0, "a"): 0, (0, "b"): 1, (1, "a"): 1},
    # finite index 5, non-normal stabiliser of a point (co-amenable)
    "Stab(0) in <(0 1 2 3 4), (0 1)>": perm_core([1, 2, 3, 4, 0], [1, 0, 2, 3, 4]),
}

if __name__ == "__main__":
    ok = True
    for name, core in EXAMPLES.items():
        f, W = counts(make_member(core))
        g = rhs(W)
        match = f == g
        ok &= match
        print(f"{name}: f_n = {f}")
        print(f"{' ' * len(name)}  rhs = {g}  match={match}")
    print("ALL MATCH" if ok else "MISMATCH")
