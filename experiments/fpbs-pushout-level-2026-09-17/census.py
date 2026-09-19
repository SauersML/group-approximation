"""Census of the fold triple group at small normal levels G = L/N.

For each level: |G|, |Kbar|, t, |N/M| from coset enumeration of
Ghat = L/<<K cap N>>^L (None = more than maxcos cosets, finiteness undecided),
and k_u(G) = dim ker of right multiplication by u' = 1 - a b^-1 - a on F_p[G]
for p = 2, 3 (u' is a conjugate of the Fox element u = 1 - c - cb, so this is the
Fox certificate; it equals dim H_1(T_G; F_p)).
"""
import random
import sys
import numpy as np
from pushout import census_one, rand_perm, psl2_perms, pmul, pinv


def elements(al, be):
    e = tuple(range(len(al)))
    idx = {e: 0}
    order = [e]
    i = 0
    while i < len(order):
        g = order[i]
        i += 1
        for s in (al, be):
            h = pmul(g, s)
            if h not in idx:
                idx[h] = len(order)
                order.append(h)
    return order, idx


def rank_mod_p(M, p):
    M = M.copy() % p
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c] % p:
                piv = i
                break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
        if r == rows:
            break
    return r


def fox_k(al, be, p):
    order, idx = elements(al, be)
    n = len(order)
    x1 = pmul(al, pinv(be))  # a b^-1
    M = np.zeros((n, n), dtype=np.int64)
    for i, g in enumerate(order):
        M[i, i] += 1
        M[i, idx[pmul(g, x1)]] -= 1
        M[i, idx[pmul(g, al)]] -= 1
    return n - rank_mod_p(M, p)


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]))
    fams = sys.argv[2].split(",")
    trials = int(sys.argv[3])
    maxcos = int(sys.argv[4]) if len(sys.argv) > 4 else 200000
    for fam in fams:
        for _ in range(trials):
            if fam.startswith("sym"):
                n = int(fam[3:])
                al, be = rand_perm(n, rng), rand_perm(n, rng)
            else:
                al, be = psl2_perms(int(fam[3:]), rng)
            nG, nK, t, I = census_one(al, be, maxcos=maxcos)
            k2, k3 = fox_k(al, be, 2), fox_k(al, be, 3)
            nm = None if I is None else I // t
            print("%-6s |G|=%-4d |Kbar|=%-4d t=%-3d |N/M|=%-6s k_u(F2)=%d k_u(F3)=%d"
                  % (fam, nG, nK, t, nm, k2, k3), flush=True)
