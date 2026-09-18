"""Exact computation of the sum-invariant characters of a contracting self-similar group.

Theorem used (see research note): with nucleus N, a function I: N -> Q with I(1)=0 extends to a
sum-invariant character chi(g) = sum_{|v|=k} I(g|_v) (k >= L(g)) iff
 (i)  I(n) = sum_x I(n|_x) for n in N, and
 (ii) chi(n1 n2) = I(n1) + I(n2) for all n1, n2 in N,
where chi(n1 n2) is expanded through sections until they land in N.
"""
from autgrp import *
from fractions import Fraction
import sys
sys.setrecursionlimit(100000)

def nullspace(rows, n):
    """rows: list of dict col->Fraction; returns basis of solutions of rows*x=0 (list of lists)."""
    M = [dict(r) for r in rows if r]
    piv = {}
    red = []
    for r in M:
        r = {k: v for k, v in r.items() if v != 0}
        for c, pr in red:
            if c in r:
                f = r[c]
                for k, v in pr.items():
                    r[k] = r.get(k, 0) - f * v
                r = {k: v for k, v in r.items() if v != 0}
        if not r:
            continue
        c = min(r)
        f = r[c]
        r = {k: v / f for k, v in r.items()}
        # back-substitute into previous
        new = []
        for c2, pr in red:
            if c in pr:
                g = pr[c]
                pr = dict(pr)
                for k, v in r.items():
                    pr[k] = pr.get(k, 0) - g * v
                pr = {k: v for k, v in pr.items() if v != 0}
            new.append((c2, pr))
        red = new + [(c, r)]
    pivots = {c for c, _ in red}
    free = [j for j in range(n) if j not in pivots]
    basis = []
    for f in free:
        x = [Fraction(0)] * n
        x[f] = Fraction(1)
        for c, pr in red:
            x[c] = -pr.get(f, 0)
        basis.append(x)
    return basis

def sum_invariant_characters(A, verbose=False):
    N, U = nucleus(A)
    if N is None:
        raise ValueError("no nucleus found")
    U.refine()
    one = U.cls[U.id[()]]
    Ncl = [c for c in N if c != one]
    col = {c: i for i, c in enumerate(Ncl)}
    n = len(Ncl)
    memo = {}
    def expand(w):
        i = U.add(w)
        if U.cls is None:
            U.refine()
        c = U.cls[i]
        if c == one:
            return {}
        if c in col:
            return {col[c]: Fraction(1)}
        if c in memo:
            return memo[c]
        p, ks = A.act(A.reduce(w))
        out = {}
        for k in ks:
            for j, v in expand(k).items():
                out[j] = out.get(j, 0) + v
        memo[c] = out
        return out
    rows = []
    # (i) sum invariance on N
    for c in Ncl:
        w = N[c]
        p, ks = A.act(w)
        r = {col[c]: Fraction(1)}
        for k in ks:
            kc = U.cls[U.add(k)] if U.cls is not None else None
            U.refine()
            kc = U.cls[U.id[A.reduce(k)]]
            if kc != one:
                r[col[kc]] = r.get(col[kc], Fraction(0)) - 1
        rows.append(r)
    # (ii) additivity on pairs; refine once after adding all products
    prods = [(c1, c2, A.reduce(N[c1] + N[c2])) for c1 in Ncl for c2 in Ncl]
    for _, _, w in prods:
        U.add(w)
    U.refine()
    one = U.cls[U.id[()]]
    col = {U.cls[U.id[N[c]]]: col[c] for c in Ncl}
    rows2 = []
    for c1, c2, w in prods:
        e = expand(w)
        r = dict(e)
        j1 = col[U.cls[U.id[N[c1]]]]; j2 = col[U.cls[U.id[N[c2]]]]
        r[j1] = r.get(j1, Fraction(0)) - 1
        r[j2] = r.get(j2, Fraction(0)) - 1
        rows2.append(r)
    basis = nullspace(rows + rows2, n)
    names = {col[U.cls[U.id[N[c]]]]: N[c] for c in Ncl}
    return basis, names, N, U
