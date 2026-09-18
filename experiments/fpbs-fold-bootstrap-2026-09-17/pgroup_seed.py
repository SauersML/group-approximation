#!/usr/bin/env python3
"""Fold-bootstrap seed densities on the Zassenhaus p-quotients F_2/D_{c+1}.

F_2/D_{c+1} is the image of F_2 = <a,b> under the Magnus map
a -> 1+X, b -> 1+Y into units of F_p<X,Y>/(degree > c).  D_{c+1} is
fully invariant, and phi: a -> a, b -> b a b^-2 is invertible mod the
Frattini subgroup (det of phi_ab is -1), so phi induces an automorphism of
F_2/D_{c+1}.  Hence each quotient is a quotient of Gamma_mal compatible with
the stage shift, and the chain is theta-invariant with trivial intersection.
Stage pair H_n <= H_{n+1} maps, after that automorphism, to the standard
generators (a, b) with K = <a, b a b^-2>.

Usage: pgroup_seed.py p cmax trials cap
"""
import random
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bootstrap_seed import Bootstrap, f2_kernel_dim
from prune_scale import greedy_seeds, prune


def words(c):
    idx = {}
    lst = []
    for l in range(c + 1):
        for v in range(2 ** l):
            w = tuple((v >> (l - 1 - j)) & 1 for j in range(l))
            idx[w] = len(lst)
            lst.append(w)
    return lst, idx


def magnus_quotient(p, c, cap):
    lst, idx = words(c)
    D = len(lst)
    app = [[None] * D, [None] * D]
    for i, w in enumerate(lst):
        if len(w) < c:
            app[0][i] = idx[w + (0,)]
            app[1][i] = idx[w + (1,)]

    def rmul(P, s):
        Q = list(P)
        a = app[s]
        for i in range(D):
            j = a[i]
            if j is not None and P[i]:
                Q[j] = (Q[j] + P[i]) % p
        return tuple(Q)

    one = tuple([1] + [0] * (D - 1))
    elts = [one]
    pos = {one: 0}
    ra, rb = [], []
    i = 0
    while i < len(elts):
        P = elts[i]
        for s, tab in ((0, ra), (1, rb)):
            Q = rmul(P, s)
            j = pos.get(Q)
            if j is None:
                j = len(elts)
                pos[Q] = j
                elts.append(Q)
                if len(elts) > cap:
                    return None
            tab.append(j)
        i += 1
    return ra, rb


def main():
    p, cmax, trials, cap = (int(x) for x in sys.argv[1:5])
    rng = random.Random(1917 + p)
    for c in range(1, cmax + 1):
        res = magnus_quotient(p, c, cap)
        if res is None:
            print(dict(p=p, c=c, note="order exceeds cap %d" % cap), flush=True)
            break
        ra, rb = res
        n = len(ra)
        bs = Bootstrap(ra, rb)
        best_g, best_p = None, None
        for _ in range(trials):
            s = greedy_seeds(bs, rng)
            best_g = len(s) if best_g is None else min(best_g, len(s))
            if n <= 20000:
                s2 = prune(bs, s, rng)
                best_p = len(s2) if best_p is None else min(best_p, len(s2))
        lb = f2_kernel_dim(bs) if (p == 2 and n <= 5000) else None
        print(dict(p=p, c=c, n=n, greedy=best_g, greedy_ratio=round(best_g / n, 5),
                   pruned=best_p,
                   pruned_ratio=None if best_p is None else round(best_p / n, 5),
                   f2_lower=lb), flush=True)


if __name__ == "__main__":
    main()
