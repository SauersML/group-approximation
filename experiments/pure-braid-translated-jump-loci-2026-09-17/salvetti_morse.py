#!/usr/bin/env python3
"""Bestvina--Brady ascending links on the Salvetti complex of the braid arrangement.

X = Salvetti complex of the (real) braid arrangement in R^n.  It is a finite regular
CW complex with pi_1 = P_n and contractible universal cover (Deligne; Salvetti).
  * chambers C  <-> permutations w (x_{w1} < ... < x_{wn}),
  * faces F     <-> ordered set partitions (blocks B_1 < ... < B_k),
  * cells <C,F> for F <= C, dim = n - k, vertex set = star(F) = chambers >= F,
  * <D,G> <= <C,F>  iff  F <= G (G refines F)  and  D = G o C.

A character chi = sum a_ij omega_ij is represented by the real 1-cocycle
    d(edge crossing H_ij) = a_ij / 2 + eta(head) - eta(tail)
(both halves of every cell boundary cross each wall of the cell once, so d is a
cocycle; the meridian of H_ij has value a_ij).  Heights of lifted vertices of the
cell <C',F>, relative to C', are f_{C'}(D) = sum_{ij sep C',D} a_ij/2 + eta(D).

Morse function on the barycentric subdivision: h(sigma) = min vertex height + eps dim.
If every cell has a unique lowest vertex, the ascending link of the barycentre of a
cell of positive dimension is (ball) * (something), hence contractible, and the
ascending link of a vertex C is the order complex of the down-closed subposet
    Asc(C) = { <C',F> : F < C, C' >= F, C is the unique argmin of f_{C'} on star(F) }.
Bestvina--Brady: if every Asc(C) is (m-1)-connected then [chi] in Sigma^m(P_n)
(homological version: (m-1)-acyclic gives Sigma^m(P_n; Z)).
"""
import itertools, random, sys
from fractions import Fraction
import numpy as np

def pairs(n):
    return [(a, b) for a in range(n) for b in range(a + 1, n)]

def faces_below(C):
    """ordered set partitions F <= C: cut C's sequence into consecutive blocks"""
    n = len(C)
    out = []
    for cuts in itertools.product((0, 1), repeat=n - 1):
        blocks, cur = [], [C[0]]
        for i in range(1, n):
            if cuts[i - 1]:
                blocks.append(frozenset(cur)); cur = [C[i]]
            else:
                cur.append(C[i])
        blocks.append(frozenset(cur))
        out.append(tuple(blocks))
    return out

def star(F):
    res = [()]
    for B in F:
        res = [r + p for r in res for p in itertools.permutations(sorted(B))]
    return res

def compose(G, C):
    """G o C: order each block of G as in C"""
    pos = {x: i for i, x in enumerate(C)}
    return tuple(x for B in G for x in sorted(B, key=pos.get))

def refines(G, F):
    """G refines F (F <= G as faces): each block of G inside a block of F, order kept"""
    i = 0
    for B in F:
        rem = set(B)
        while rem:
            if i >= len(G) or not G[i] <= rem:
                return False
            rem -= G[i]; i += 1
    return i == len(G)

def sepval(a, C1, C2):
    p1 = {x: i for i, x in enumerate(C1)}
    p2 = {x: i for i, x in enumerate(C2)}
    s = 0
    for (i, j), v in a.items():
        if (p1[i] < p1[j]) != (p2[i] < p2[j]):
            s += v
    return s

class Morse:
    def __init__(self, n, a, eta):
        self.n, self.a, self.eta = n, a, eta

    def asc_poset(self, C):
        """elements (C', F) with C unique argmin; returns list and order relation"""
        els = []
        for F in faces_below(C):
            if len(F) == self.n:
                continue
            S = star(F)
            for Cp in S:
                vals = {D: sepval(self.a, Cp, D) + self.eta[D] for D in S}
                vC = vals[C]
                if all(v > vC for D, v in vals.items() if D != C):
                    els.append((Cp, F))
                elif sum(1 for v in vals.values() if v == vC) > 1 and \
                        min(vals.values()) == vC:
                    raise ValueError("tie: lowest vertex not unique")
        return els

def leq(x, y):
    """x = (D,G) <= y = (C',F) in the Salvetti face order"""
    (D, G), (Cp, F) = x, y
    return refines(G, F) and D == compose(G, Cp)

def order_complex_homology(els, p=1000003, maxdim=None):
    """reduced Betti numbers over F_p of the order complex of the poset els"""
    N = len(els)
    if N == 0:
        return [-1]  # empty: reduced H_{-1} = 1
    less = [[j for j in range(N) if j != i and leq(els[j], els[i])] for i in range(N)]
    # chains: sorted increasing (by poset); build by extending downward
    chains = {0: [(i,) for i in range(N)]}
    k = 0
    while chains[k] and (maxdim is None or k < maxdim + 1):
        nxt = []
        for c in chains[k]:
            for j in less[c[0]]:
                nxt.append((j,) + c)
        k += 1
        chains[k] = nxt
    idx = {k: {c: i for i, c in enumerate(chains[k])} for k in chains}
    ranks = {}
    from salvetti_jump import rank_mod
    for k in range(1, len(chains)):
        if not chains[k] or not chains[k - 1]:
            ranks[k] = 0
            continue
        M = np.zeros((len(chains[k - 1]), len(chains[k])), dtype=np.int64)
        for j, c in enumerate(chains[k]):
            for t in range(len(c)):
                f = c[:t] + c[t + 1:]
                M[idx[k - 1][f], j] += (-1) ** t
        ranks[k] = rank_mod(M, p)
    betti = []
    top = len(chains) - 1
    for k in range(0, top + 1):
        nk = len(chains[k])
        if nk == 0:
            break
        b = nk - ranks.get(k, 0) - ranks.get(k + 1, 0)
        if k == 0:
            b -= 1
        betti.append(b)
    return betti

def random_eta(n, amp, rng, den=10**6):
    """eta uniform in [-amp, amp] with denominator den (generic tie-breaking)"""
    return {C: Fraction(rng.randrange(-amp * den, amp * den + 1), den)
            for C in itertools.permutations(range(n))}
