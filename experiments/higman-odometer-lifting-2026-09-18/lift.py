#!/usr/bin/env python3
"""Level-by-level lifting of models of H4(3)/<<[a,c]^2>> on the binary tree with a = odometer.

W_(k+1) = F_2^(2^k) x| W_k (switches at level-k vertices).  Lifting (a,b,c,d) from W_k to W_(k+1)
with fixed a-lift (odometer) is an inhomogeneous F_2-linear system in the switch vectors of b,c,d.
Right actions, GAP conventions: gh = first g then h, x^y = y^-1 x y, [x,y] = x^-1 y^-1 x y.
Vertex x of level k is an integer mod 2^k; its children at level k+1 are x and x + 2^k.
"""
import random, sys

GENS = "abcd"
# relators as lists of (generator index, +-1)
def w(s):
    out = []
    for ch in s:
        out.append((GENS.index(ch.lower()), 1 if ch.islower() else -1))
    return out
import os
BASE = int(os.environ.get("HBASE", "3"))   # H4(n): b^a = b^n, ...; default n = 3
def conjrel(x, y, n):  # x^y x^-n
    return w(y.upper() + x + y + x.upper() * n)
RELS = [conjrel("b", "a", BASE), conjrel("c", "b", BASE), conjrel("d", "c", BASE), conjrel("a", "d", BASE),
        w("ACacACac")]                           # [a,c]^2

def inv(p):
    q = [0] * len(p)
    for i, j in enumerate(p):
        q[j] = i
    return q

def evalword(perms, word):
    N = len(perms[0]); invs = [inv(p) for p in perms]
    res = list(range(N))
    for g, s in word:
        p = perms[g] if s == 1 else invs[g]
        res = [p[x] for x in res]
    return res

def check(perms):
    N = len(perms[0])
    return all(evalword(perms, r) == list(range(N)) for r in RELS)

def system(perms, free=(1, 2, 3), fixed=None):
    """Equations sum of switch bits = 0 per relator per point. Returns list of (mask, rhs)."""
    N = len(perms[0]); invs = [inv(p) for p in perms]
    col = {g: i for i, g in enumerate(free)}
    eqs = []
    for r in RELS:
        for x in range(N):
            mask = 0; rhs = 0; p = x
            for g, s in r:
                if s == -1:
                    p = invs[g][p]
                if g in col:
                    mask ^= 1 << (col[g] * N + p)
                elif fixed[g][p]:
                    rhs ^= 1
                if s == 1:
                    p = perms[g][p]
            eqs.append((mask, rhs))
    return eqs

def solve(eqs, nvars):
    """Gauss-Jordan over F_2. Returns (piv, free) with piv[bit] = (mask, rhs) in RREF, or None."""
    piv = {}
    for m, r in eqs:
        for hb, (pm, pr) in piv.items():
            if (m >> hb) & 1:
                m ^= pm; r ^= pr
        if m == 0:
            if r:
                return None
            continue
        hb = m.bit_length() - 1
        for k2 in list(piv):
            pm, pr = piv[k2]
            if (pm >> hb) & 1:
                piv[k2] = (pm ^ m, pr ^ r)
        piv[hb] = (m, r)
    free = [i for i in range(nvars) if i not in piv]
    return piv, free

def sample(sol, nvars, rng, zero=False):
    piv, free = sol
    val = 0
    if not zero:
        for f in free:
            if rng.random() < 0.5:
                val |= 1 << f
    fv = val
    for hb, (m, r) in piv.items():
        if r ^ (bin(m & fv).count("1") & 1):
            val |= 1 << hb
    return val

def lift(perms, vecs):
    N = len(perms[0]); out = []
    for p, v in zip(perms, vecs):
        q = [0] * (2 * N)
        for x in range(N):
            for e in (0, 1):
                q[x + e * N] = p[x] + ((e ^ v[x]) * N)
        out.append(q)
    return out

def order(p):
    from math import lcm
    seen = [False] * len(p); o = 1
    for i in range(len(p)):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]; l += 1
            o = lcm(o, l)
    return o
