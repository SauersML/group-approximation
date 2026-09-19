#!/usr/bin/env python3
"""Exact cone-table arithmetic for the (two-radix) odometer host H on X = {0,1} x Zhat,
and a search for elements of the near group R_nu = <lambda(A_0), lambda(A_1), s>
supported in a proper cone with a non-unit slope.

A leaf is (e, a, M, e2, B, M2, G): the cone {e} x (a + M Zhat), 0 <= a < M, maps by
    a + M t  |->  (e2, B + M2 (t + G)),     0 <= B < M2.
An element is a list of leaves whose domains partition X.  Composition is exact integer
arithmetic.  Works for any set of radices; moduli are products of radix powers.
"""
import sys, itertools, random, time
from math import gcd
from itertools import permutations

def lcm(a, b):
    return a // gcd(a, b) * b

def modinv(a, m):
    """Inverse of a mod m (gcd(a, m) = 1), extended Euclid (python 3.6 has no pow(a, -1, m))."""
    r0, r1, s0, s1 = m, a % m, 0, 1
    while r1:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if r0 != 1:
        raise ValueError("not invertible")
    return s0 % m

def compose(g2, g1):
    """Return g2 o g1 (apply g1 first)."""
    idx = {}
    for L in g2:
        idx.setdefault(L[0], {}).setdefault(L[2], {})[L[1]] = L
    out = []
    for (e1, a1, M1, f1, b1, N1, G1) in g1:
        bymod = idx[f1]
        for M2, table in bymod.items():
            d = gcd(N1, M2)
            K = M2 // d
            kappa = N1 // d
            if K <= len(table):
                taus = range(K)
            else:
                inv = modinv(kappa % K, K) if K > 1 else 0
                taus = []
                for a2 in table:
                    c = a2 - b1 - N1 * G1
                    if c % d:
                        continue
                    taus.append(((c // d) * inv) % K if K > 1 else 0)
            for tau in taus:
                z0 = b1 + N1 * (tau + G1)
                r = z0 % M2
                L2 = table.get(r)
                if L2 is None:
                    continue
                (_, a2, _, f2, b2, N2, G2) = L2
                u0 = (z0 - a2) // M2
                A = a1 + M1 * tau
                Mn = M1 * K
                Np = N2 * kappa
                w0 = b2 + N2 * (u0 + G2)
                B = w0 % Np
                G = (w0 - B) // Np
                out.append((e1, A, Mn, f2, B, Np, G))
    return out

def inverse(g):
    return [(f, b, N, e, a, M, -G) for (e, a, M, f, b, N, G) in g]

def is_identity_leaf(L):
    e, a, M, f, b, N, G = L
    return e == f and M == N and a == b and G == 0

def merge(g, radices):
    """Merge complete sibling families whose maps restrict one parent map."""
    g = list(g)
    changed = True
    while changed:
        changed = False
        for h in radices:
            fam = {}
            rest = []
            for L in g:
                e, a, M, f, b, N, G = L
                if M % h == 0 and N % h == 0:
                    Mp = M // h
                    ap = a % Mp
                    k = (a - ap) // Mp
                    fam.setdefault((e, Mp, ap), {})[k] = L
                else:
                    rest.append(L)
            newg = rest
            for (e, Mp, ap), kids in fam.items():
                ok = False
                if len(kids) == h:
                    L0 = kids[0]
                    f, N = L0[3], L0[5]
                    Np = N // h
                    V0 = L0[4] + N * L0[6]
                    ok = True
                    for k in range(h):
                        Lk = kids[k]
                        if Lk[3] != f or Lk[5] != N:
                            ok = False; break
                        Vk = Lk[4] + Lk[5] * Lk[6]
                        if Vk != V0 + Np * k:
                            ok = False; break
                    if ok:
                        B = V0 % Np
                        G = (V0 - B) // Np
                        newg.append((e, ap, Mp, f, B, Np, G))
                        changed = True
                if not ok:
                    newg.extend(kids.values())
            g = newg
    return g

def mul(*gs, radices):
    """mul(a, b, c) = a o b o c (rightmost applied first)."""
    r = gs[-1]
    for g in reversed(gs[:-1]):
        r = merge(compose(g, r), radices)
    return r

def evaluate(g, e, y):
    """Evaluate on an integer point (e, y) (y may be negative)."""
    for (e1, a, M, f, b, N, G) in g:
        if e1 == e and (y - a) % M == 0:
            t = (y - a) // M
            return (f, b + N * (t + G))
    raise ValueError("no leaf")

# ---------- groups ----------
def perm_mul(p, q):  # p o q
    return tuple(p[q[i]] for i in range(len(q)))

def alt_group(n):
    els = []
    for p in permutations(range(n)):
        inv = sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])
        if inv % 2 == 0:
            els.append(p)
    return els

def cyclic_group(n):
    return [tuple((i + k) % n for i in range(n)) for k in range(n)]

def labeling(group, forced=None):
    """Nonidentity elements -> digits 1..h.  forced: dict element->digit."""
    ident = tuple(range(len(group[0])))
    non = [x for x in group if x != ident]
    h = len(non)
    lab = [None] * (h + 1)
    forced = forced or {}
    for x, d in forced.items():
        lab[d] = x
    rest = [x for x in non if x not in forced]
    it = iter(rest)
    for d in range(1, h + 1):
        if lab[d] is None:
            lab[d] = next(it)
    digit = {lab[d]: d for d in range(1, h + 1)}
    return ident, lab, digit, h

def lam(x, G, side):
    """Left multiplication by x in factor `side` (0 or 1): prepends on words of the other type,
    acts on the first digit of words of its own type.  side 0 words live in root 0."""
    ident, lab, digit, h = G
    own, other = side, 1 - side
    leaves = []
    c = digit[x]
    # root `other` (whole) -> cone (own, c mod h)
    leaves.append((other, 0, 1, own, c % h, h, 1 if c == h else 0))
    for r in range(h):
        d = r if r >= 1 else h
        y = lab[d]
        xy = perm_mul(x, y)
        corr_d = 1 if d == h else 0
        if xy == ident:
            leaves.append((own, r, h, other, 0, 1, -corr_d))
        else:
            dp = digit[xy]
            leaves.append((own, r, h, own, dp % h, h, (1 if dp == h else 0) - corr_d))
    return leaves

S_SHIFT = [(0, 0, 1, 1, 0, 1, 0), (1, 0, 1, 0, 0, 1, 1)]

def support_report(g):
    non = [L for L in g if not is_identity_leaf(L)]
    roots = sorted(set(L[0] for L in non))
    slopes = sorted(set((L[5], L[2]) for L in non if L[5] != L[2]))
    nonunit = [L for L in non if L[5] != L[2]]
    return non, roots, nonunit

def detector(g):
    """HIT iff nontrivial, all moved points in one root (a proper cone of X), and some slope != 1."""
    non, roots, nonunit = support_report(g)
    return len(non) > 0 and len(roots) == 1 and len(nonunit) > 0
