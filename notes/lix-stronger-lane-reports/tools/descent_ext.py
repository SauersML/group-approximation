#!/usr/bin/env python3
"""sp-descent model test 1: the two-letter descent, re-described as exterior algebra.

sp-design's `steenrod_descent.py` runs the descent on words in {f, g} with Koszul signs.
This file re-describes exactly the same computation inside the exterior algebra
Lambda(xi_0, ..., xi_{p-1}) over Z, and checks the re-description against a direct
re-implementation of the word model.  The dictionary is

    word w  <->  e_S,  S = { j : w_j = g }   (f = degree 0, g = degree 1)

    D   = left multiplication by  sigma := xi_0 + ... + xi_{p-1}
    H   = d/d xi_0   (the left partial derivative; H(g (x) ...) = f (x) ...)
    T   = the graded ALGEBRA automorphism  xi_j |-> xi_{j-1 mod p}
    N   = sum_k T^k

Everything is done over Z; reductions mod p are taken at the end only.

Run:  python3 descent_ext.py [p ...]
"""
import sys
from itertools import combinations, product

# --------------------------------------------------------------- exterior algebra
# An element is a dict  frozenset-as-sorted-tuple -> int coefficient.


def wedge_gen(j, S):
    """xi_j ^ e_S = (-1)^{#(S cap [0,j))} e_{S u {j}}; 0 if j in S.
    Returns (sign, newS) or None."""
    if j in S:
        return None
    k = sum(1 for i in S if i < j)
    return ((-1) ** k, tuple(sorted(S + (j,))))


def partial(j, S):
    """d/d xi_j applied to e_S.  Returns (sign, newS) or None."""
    if j not in S:
        return None
    k = S.index(j)
    return ((-1) ** k, tuple(x for x in S if x != j))


def addto(out, S, c):
    if c:
        out[S] = out.get(S, 0) + c
        if out[S] == 0:
            del out[S]


def op_D(p, v):
    """D = sigma ^ (-)."""
    out = {}
    for S, c in v.items():
        for j in range(p):
            r = wedge_gen(j, S)
            if r:
                addto(out, r[1], r[0] * c)
    return out


def op_H(p, v):
    """H = d/d xi_0."""
    out = {}
    for S, c in v.items():
        r = partial(0, S)
        if r:
            addto(out, r[1], r[0] * c)
    return out


def op_wedge0(p, v):
    """xi_0 ^ (-), the adjoint of H."""
    out = {}
    for S, c in v.items():
        r = wedge_gen(0, S)
        if r:
            addto(out, r[1], r[0] * c)
    return out


def _perm_sign(seq):
    """sign of the permutation sorting seq (all entries distinct)."""
    s = 1
    a = list(seq)
    for i in range(len(a)):
        for j in range(i + 1, len(a)):
            if a[i] > a[j]:
                s = -s
    return s


def op_T(p, v, inv=False):
    """T = the algebra map xi_j |-> xi_{j-1 mod p}   (inv: xi_j |-> xi_{j+1})."""
    out = {}
    d = 1 if not inv else -1
    for S, c in v.items():
        img = [(j - d) % p for j in S]
        addto(out, tuple(sorted(img)), _perm_sign(img) * c)
    return out


def op_N(p, v):
    out = {}
    cur = dict(v)
    for _ in range(p):
        for S, c in cur.items():
            addto(out, S, c)
        cur = op_T(p, cur)
    return out


def op_sub(a, b):
    out = dict(a)
    for S, c in b.items():
        addto(out, S, -c)
    return out


def op_s(p, v, inv=False):
    """T - 1  (inv: T^{-1} - 1)."""
    return op_sub(op_T(p, v, inv=inv), v)


# --------------------------------------------------------------- the word model (sp-design)
# a word is a tuple of 0/1, 1 = g.


def w_deg(w):
    return sum(w)


def wD(p, v):
    out = {}
    for w, c in v.items():
        pre = 0
        for j in range(p):
            if w[j] == 0:
                w2 = w[:j] + (1,) + w[j + 1:]
                addto(out, w2, ((-1) ** pre) * c)
            pre += w[j]
    return out


def wH(p, v):
    out = {}
    for w, c in v.items():
        if w[0] == 1:
            addto(out, (0,) + w[1:], c)
    return out


def wT(p, v):
    out = {}
    for w, c in v.items():
        d0 = w[0]
        s = (-1) ** (d0 * (w_deg(w) - d0))
        addto(out, w[1:] + (w[0],), s * c)
    return out


def wN(p, v):
    out = {}
    cur = dict(v)
    for _ in range(p):
        for k, c in cur.items():
            addto(out, k, c)
        cur = wT(p, cur)
    return out


def w_of_S(p, S):
    return tuple(1 if j in S else 0 for j in range(p))


def S_of_w(w):
    return tuple(j for j, b in enumerate(w) if b)


def dict_ext_to_word(p, v):
    return {w_of_S(p, S): c for S, c in v.items()}


# --------------------------------------------------------------- the primal descent


def red(v, mod):
    if mod is None:
        return {k: c for k, c in v.items() if c}
    return {k: c % mod for k, c in v.items() if c % mod}


def primal_descent(p, verbose=False, mod=None):
    """A_0 = xi_0 ^ ... ^ xi_{p-1}; while Widx > 0: Y = H(A); A = op(Y); Widx -= 1.
    op = N when Widx is even, T - 1 when odd.  Returns (c_1, [Y levels])."""
    A = {tuple(range(p)): 1}
    Widx = p - 1
    levels = []
    cocyc, prim = [], []
    while Widx > 0:
        cocyc.append(red(op_D(p, A), mod) == {})
        Y = op_H(p, A)
        prim.append(red(op_sub(op_D(p, Y), A), mod) == {})
        A = red(op_N(p, Y) if Widx % 2 == 0 else op_s(p, Y), mod)
        levels.append((Widx, "N" if Widx % 2 == 0 else "T-1", Y))
        Widx -= 1
    levels_ok = (all(cocyc), all(prim))
    # c_1 = coefficient of the word (g, f, ..., f) = e_{{0}} = xi_0
    return A.get((0,), 0), levels, A, levels_ok


# --------------------------------------------------------------- the dual descent


def dual_descent(p, verbose=False, mod=None):
    """x_0 = xi_0;  x_{k+1} = xi_0 ^ N( xi_0 ^ (T^{-1} - 1) x_k );  c_1 = [omega] x_m."""
    x = {(0,): 1}
    xs = [dict(x)]
    m = (p - 1) // 2
    for _ in range(m):
        x = red(op_wedge0(p, op_N(p, op_wedge0(p, op_s(p, x, inv=True)))), mod)
        xs.append(dict(x))
    return x.get(tuple(range(p)), 0), xs


# --------------------------------------------------------------- domino hypothesis


def dominoes(p, k):
    """sets of k pairwise disjoint pairs {a, a+1} inside {1, ..., p-1}."""
    out = []
    for cs in combinations(range(1, p - 1), k):
        ok = all(cs[i] + 1 < cs[i + 1] for i in range(k - 1))
        if ok:
            out.append(cs)
    return out


def domino_element(p, k):
    """X_k := sum over k-domino configurations D of  xi_0 ^ e_{union D}."""
    out = {}
    for cs in dominoes(p, k):
        S = (0,) + tuple(sorted([j for a in cs for j in (a, a + 1)]))
        addto(out, S, 1)
    return out


def scal(v, c):
    return {k: c * val for k, val in v.items()}


def show(p, v, limit=14):
    if not v:
        return "0"
    items = sorted(v.items())
    if len(items) > limit:
        return f"<{len(items)} terms>"
    return " + ".join(f"{c}*e{list(S)}" for S, c in items)



# --------------------------------------------------------------- main
if __name__ == "__main__":
    primes = [int(a) for a in sys.argv[1:]] or [3, 5, 7, 11, 13]

    def factorial(n):
        r = 1
        for i in range(2, n + 1):
            r *= i
        return r

    print("### 0. the exterior re-description agrees with the word model")
    for p in [3, 5, 7]:
        bad = 0
        for S in [tuple(c) for k in range(p + 1) for c in combinations(range(p), k)]:
            v = {S: 1}
            w = {w_of_S(p, S): 1}
            for name, oe, ow in (("D", op_D, wD), ("H", op_H, wH),
                                 ("T", op_T, wT), ("N", op_N, wN)):
                if dict_ext_to_word(p, oe(p, v)) != ow(p, w):
                    bad += 1
        print(f"  p={p}: mismatching (operator, basis element) pairs: {bad}")

    print()
    print("### 1. D H + H D = 1 and D o D = 0 on the p-fold tensor power, over Z")
    for p in [3, 5, 7]:
        bad1 = bad2 = 0
        for k in range(p + 1):
            for S in combinations(range(p), k):
                v = {tuple(S): 1}
                lhs = op_D(p, op_H(p, v))
                for kk, c in op_H(p, op_D(p, v)).items():
                    addto(lhs, kk, c)
                if op_sub(lhs, v):
                    bad1 += 1
                if op_D(p, op_D(p, v)):
                    bad2 += 1
        print(f"  p={p}: DH+HD-1 failures {bad1}, DD failures {bad2}")

    print()
    print("### 2. the primal descent: value over Z, and mod p")
    for p in primes:
        cz, lz, _, okz = primal_descent(p, mod=None)
        cp, lp, _, okp = primal_descent(p, mod=p)
        m = (p - 1) // 2
        mf = factorial(m)
        print(f"  p={p:3d}: over Z c_1 = {cz:24d}  m! = {mf:24d}  equal {cz == mf}"
              f" | cocycle/primitive over Z {okz} | mod p c_1 = {cp}, m! mod p = {mf % p},"
              f" equal {cp == mf % p} | cocycle/primitive mod p {okp}")

    print()
    print("### 3. the final primitive Y_last = c_1 * sum_j j xi_j (mod p)")
    for p in primes:
        cp, lp, _, _ = primal_descent(p, mod=p)
        Ylast = red(lp[-1][2], p)
        ok = all((Ylast.get((j,), 0) - cp * j) % p == 0 for j in range(p))
        print(f"  p={p:3d}: matches c_1*j mod p: {ok}   Y_last = "
              f"{[Ylast.get((j,),0) for j in range(p)]}")

    print()
    print("### 4. the dual (building-up) descent gives the same constant")
    for p in primes:
        cz, _, _, _ = primal_descent(p, mod=None)
        dz, _ = dual_descent(p, mod=None)
        cp, _, _, _ = primal_descent(p, mod=p)
        dp, _ = dual_descent(p, mod=p)
        print(f"  p={p:3d}: over Z primal {cz} dual {dz} equal {cz == dz};"
              f"  mod p primal {cp} dual {dp} equal {cp == dp}")

    print()
    print("### 5. x_k of the dual descent versus  k! * X_k  (X_k = the k-domino sum), over Z")
    for p in primes:
        _, xs = dual_descent(p, mod=None)
        m = (p - 1) // 2
        row = []
        for k in range(m + 1):
            pred = scal(domino_element(p, k), factorial(k))
            row.append("YES" if op_sub(xs[k], pred) == {} else "NO")
        print(f"  p={p:3d}: k = 0..{m}: {row}")
        if p <= 7:
            for k in range(m + 1):
                print(f"      x_{k} = {show(p, xs[k], 20)}")
