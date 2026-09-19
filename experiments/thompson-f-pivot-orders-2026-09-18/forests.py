#!/usr/bin/env python3
"""Forest model of the positive monoid M of Thompson's group F, and the stubborn-set
machinery of `thompson-f-p22-monomials-admit-no-private-pivot-order` in that model.

Conventions (identical to experiments/thompson-f-2026-09-17/stubborn_core.cpp):

* `M = < x_0, x_1, ... | x_j x_i = x_i x_{j+1} (i<j) >`, normal forms
  `x_{i_1} ... x_{i_D}` with `i_1 <= ... <= i_D`.
* An element of `M` is a forest of binary trees on the roots `0, 1, 2, ...`, all but
  finitely many trivial.  `x_j z` joins roots `j` and `j+1` of `z` under a new caret.
* A tree is `0` (a leaf) or a pair `(L, R)`.  A forest is a tuple of trees.

For a finite homogeneous `S` of degree `d`, let `K = K(S)` be the number of leaves that
`S` touches, i.e. `max{ s_t + d - t + 1 : s in S, 0 <= t < d }` for `s = x_{s_0} ... x_{s_{d-1}}`
in normal form (this is what `K_of` computes).  The shortcut `1 + max{last letter + 1}` is
WRONG in general -- it gives 8 instead of 7 for `S = {x_0 x_5 x_5}` -- and is not used.
Then every `s in S`, as a forest, is a forest on `K` leaves with `d` carets and `K - d`
roots, followed by trivial trees.

TAIL SPLITTING.  Write `z in M` as `(u ; v)` with `u` the first `K` roots and `v` the rest.
Then `s z = (s.u ; v)` and every factorisation `w = s' z'` with `s' in S` has
`z' = (u' ; v)` with the SAME tail `v`.  So the private-successor count of `z` inside a set
`Z` only involves the fibre `Z_v = { u : (u;v) in Z }`, and `Z` is stubborn iff every
nonempty fibre `Z_v` is stubborn in the finite *prefix world*

    P_a(S) = { forests with exactly K roots and a carets },   |P_a| = f(K+a, K),

where `f(n,r) = (r/n) C(2n-r-1, n-1)` is the number of ordered forests of `r` binary trees
with `n` leaves.  Hence `core(M_D) != 0` iff `core(P_a) != 0` for some `a <= D`, and the
least such `D` is the least such `a`.  This is what makes the search finite with no
`letters <= L` truncation parameter.
"""
from math import comb


# ---------------------------------------------------------------- words <-> forests
def word_to_forest(w, width=None):
    """Normal-form word (non-decreasing letters) -> forest, as a tuple of trees.

    `width` is the number of roots started from; each letter consumes one, so the result has
    `width - len(w)` roots.  The default keeps `len(w) + max(w) + 2` trivial roots at the end,
    which is enough for any product used here; pass `width` explicitly when a fixed number of
    roots is needed."""
    w = list(w)
    n = (width if width is not None else 2 * len(w) + (max(w) if w else 0) + 2)
    trees = [0] * n
    for j in reversed(w):
        if j + 1 >= len(trees):
            raise ValueError("width too small")
        trees = trees[:j] + [(trees[j], trees[j + 1])] + trees[j + 2:]
    return tuple(trees)


def forest_to_word(f):
    """Inverse of word_to_forest: peel root carets left to right, repeatedly."""
    trees = list(f)
    out = []
    while True:
        for j, t in enumerate(trees):
            if t != 0:
                out.append(j)
                trees = trees[:j] + [t[0], t[1]] + trees[j + 1:]
                break
        else:
            break
    return tuple(out)


def n_carets(t):
    return 0 if t == 0 else 1 + n_carets(t[0]) + n_carets(t[1])


def n_leaves(t):
    return 1 if t == 0 else n_leaves(t[0]) + n_leaves(t[1])


# ---------------------------------------------------------------- S as forests
def K_of(S):
    """Number of leaves the monomial set S touches.  Applying x_{s_t} in s = x_{s_0}...x_{s_{d-1}}
    from the right needs root s_t + 1 to still exist after d-1-t merges, so K >= s_t + d - t + 1."""
    return max(s[t] + len(s) - t + 1 for s in S for t in range(len(s)))


def mono_forest(s, K):
    """normal-form monomial s (a tuple of letters) as a forest on K leaves"""
    return word_to_forest(s, width=K)


# ---------------------------------------------------------------- forest products
def graft(s_forest, u):
    """s . u : replace leaf i of the forest s_forest by the tree u[i]."""
    it = iter(u)

    def go(t):
        if t == 0:
            return next(it)
        return (go(t[0]), go(t[1]))

    return tuple(go(t) for t in s_forest)


def peel(s_forest, w):
    """the unique u with s_forest . u == w, or None."""
    if len(w) != len(s_forest):
        return None
    out = []

    def go(t, x):
        if t == 0:
            out.append(x)
            return True
        if x == 0:
            return False
        return go(t[0], x[0]) and go(t[1], x[1])

    for t, x in zip(s_forest, w):
        if not go(t, x):
            return None
    return tuple(out)


# ---------------------------------------------------------------- prefix world P_a
def forests(r, n):
    """all ordered forests of r binary trees with n leaves in total"""
    memo = {}

    def trees(k):
        if k in memo:
            return memo[k]
        if k == 1:
            res = [0]
        else:
            res = []
            for a in range(1, k):
                for L in trees(a):
                    for R in trees(k - a):
                        res.append((L, R))
        memo[k] = res
        return res

    def rec(r, n):
        if r == 0:
            return [()] if n == 0 else []
        out = []
        for k in range(1, n - (r - 1) + 1):
            for t in trees(k):
                for rest in rec(r - 1, n - k):
                    out.append((t,) + rest)
        return out

    return rec(r, n)


def count_forests(r, n):
    if r == 0:
        return 1 if n == 0 else 0
    if n < r:
        return 0
    return r * comb(2 * n - r - 1, n - 1) // n


# ---------------------------------------------------------------- stubborn core
def stubborn_core(S, a, verbose=False):
    """maximal stubborn subset of the prefix world P_a(S); returns (P_a, core set)."""
    K = K_of(S)
    SF = [mono_forest(s, K) for s in S]
    d = len(S[0])
    U = forests(K, K + a)
    idx = {u: i for i, u in enumerate(U)}
    # successor products, and predecessor sets, computed locally
    prod = [[graft(sf, u) for sf in SF] for u in U]
    preds = {}
    for i, u in enumerate(U):
        for w in prod[i]:
            if w not in preds:
                pr = []
                for sf in SF:
                    p = peel(sf, w)
                    if p is not None:
                        pr.append(idx[p])
                preds[w] = pr
    alive = [True] * len(U)
    surv = {w: len(pr) for w, pr in preds.items()}
    changed = True
    while changed:
        changed = False
        for i in range(len(U)):
            if not alive[i]:
                continue
            c = sum(1 for w in prod[i] if surv[w] == 1)
            if c >= 2:
                alive[i] = False
                changed = True
                for w in prod[i]:
                    surv[w] -= 1
    core = [U[i] for i in range(len(U)) if alive[i]]
    # independent re-verification of stubbornness
    cset = set(core)
    for u in core:
        c = 0
        for sf in SF:
            w = graft(sf, u)
            hits = [p for p in (peel(sf2, w) for sf2 in SF) if p is not None and p in cset]
            if hits == [u]:
                c += 1
        assert c <= 1, "core not stubborn"
    return U, core


if __name__ == "__main__":
    import json
    import sys

    S = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3)]
    a = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    U, core = stubborn_core(S, a)
    print(json.dumps({"K": K_of(S), "a": a, "|P_a|": len(U),
                      "predicted": count_forests(K_of(S), K_of(S) + a),
                      "core": len(core)}))
