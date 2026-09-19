# Exact arithmetic in the nonnegative-degree part of L_k(1,2), k = F_2.
# An element with window R is a map  beta (word of length R) -> F_2-combination of words alpha, |alpha| >= R,
# standing for  sum c * s_alpha s_beta^*.  For fixed R these monomials are linearly independent in L
# (evaluate on delta_{beta w} for an aperiodic infinite word w), so this is a faithful representation of
# the subalgebra L_{>=0} (window <= R elements are refined to window R).
# Product x*y : first y rewrites the prefix beta to alpha', then x reads the first R letters of alpha'.
import itertools, random, sys
from collections import defaultdict

def words(n):
    return [''.join(p) for p in itertools.product('01', repeat=n)]

def mul(x, y, R):
    out = {}
    for beta in words(R):
        acc = defaultdict(int)
        for a1, c1 in y.get(beta, {}).items():
            g, tau = a1[:R], a1[R:]
            for a2, c2 in x.get(g, {}).items():
                acc[a2 + tau] ^= (c1 & c2)
        acc = {w: 1 for w, c in acc.items() if c}
        if acc:
            out[beta] = acc
    return out

def add(x, y):
    out = {}
    for beta in set(x) | set(y):
        acc = defaultdict(int)
        for w in x.get(beta, {}): acc[w] ^= 1
        for w in y.get(beta, {}): acc[w] ^= 1
        acc = {w: 1 for w, c in acc.items() if c}
        if acc: out[beta] = acc
    return out

def one(R):
    return {b: {b: 1} for b in words(R)}

def key_set(elts):
    ks = set()
    for e in elts:
        for beta, d in e.items():
            for w in d: ks.add((beta, w))
    return sorted(ks)

def rank_of(elts):
    # rank over F_2 of a list of elements, using python ints as bit rows
    ks = key_set(elts); idx = {k: i for i, k in enumerate(ks)}
    rows = []
    for e in elts:
        v = 0
        for beta, d in e.items():
            for w in d: v |= 1 << idx[(beta, w)]
        rows.append(v)
    basis = []  # list of (pivotbit, row)
    r = 0
    piv = {}
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in piv: v ^= piv[h]
            else:
                piv[h] = v; r += 1; break
    return r

def monomials(x, y, R, n):
    # all x^i y^j with i+j<=n
    pw_x = [one(R)]
    for _ in range(n): pw_x.append(mul(pw_x[-1], x, R))
    pw_y = [one(R)]
    for _ in range(n): pw_y.append(mul(pw_y[-1], y, R))
    return {(i, j): mul(pw_x[i], pw_y[j], R) for i in range(n + 1) for j in range(n + 1 - i)}

def hilbert(x, y, R, n):
    mons = monomials(x, y, R, n)
    return [rank_of([mons[(i, j)] for (i, j) in mons if i + j <= m]) for m in range(n + 1)]

def commutes(x, y, R):
    return mul(x, y, R) == mul(y, x, R)
