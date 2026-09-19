#!/usr/bin/env python3
"""Palindromic products of hyperelliptic 3|3 twists at level four.

Setting (Birman--Hilden, as in mod-s2-gamma4-torelli-census-is-one-thirtieth):
M_4 = pi^-1 Gamma(4) <= Mod(S_2) is isomorphic to
    K4 = Phi(Pbar),   Pbar = PMod(S_{0,6}) = P_5 / <Delta^2>,
the kernel of Pbar -> H_1(Pbar; F_2) = F_2^10 / <(1,...,1)>  (index 512).
A separating twist t_s of S_2 is the lift of T_A^2, T_A the twist about a
3|3 curve of S_{0,6}; u_A = lift of T_A is a square root of t_s.

This script
 1. builds H_1(K4) by abelianised Reidemeister--Schreier from Artin's
    presentation of P_5 plus Delta^2 (512 cosets, much smaller than the
    61440-coset braid-group computation of the census node) and re-derives
    rank 54, the 160 separating classes, rank W = 106 and gcd aug = 10;
 2. tests the palindrome  y = x x^rev,  x = T_1 ... T_10  (one 3|3 twist per
    splitting of {1..6}, any curves, any order), whose lift
    y = prod_i g_i t_{s_i} g_i^-1 (g_i = u_1...u_{i-1}) is a transversal
    product of ten separating twists, for [y] = 0 in H_1(M_4);
 3. as controls, tests random transversal products and palindromes with a
    repeated or missing splitting.
"""
import json
import os
import random
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
import pure as P  # noqa: E402

NP = len(P.PAIRS)            # 10 pure generators
ALL = (1 << NP) - 1


def canon(v):
    return v ^ ALL if v & 1 else v


COSETS = sorted({canon(v) for v in range(1 << NP)})
CIDX = {v: k for k, v in enumerate(COSETS)}
ACT = [[CIDX[canon(v ^ (1 << p))] for p in range(NP)] for v in COSETS]


def schreier():
    k = len(ACT)
    seen = [False] * k
    seen[0] = True
    tree, parent = set(), {0: None}
    queue = [0]
    for c in queue:
        for p in range(NP):
            d = ACT[c][p]
            if not seen[d]:
                seen[d] = True
                tree.add((c, p))
                parent[d] = (c, p)
                queue.append(d)
    gen = {}
    for c in range(k):
        for p in range(NP):
            if (c, p) not in tree:
                gen[(c, p)] = len(gen)
    rep = {}
    for c in range(k):
        w, d = [], c
        while parent[d] is not None:
            b, p = parent[d]
            w.append(p + 1)
            d = b
        rep[c] = tuple(reversed(w))
    return gen, rep


GEN, REP = schreier()


def trace(word, c=0, vec=None):
    """Abelianised Schreier rewriting of a pure word (letters +-(p+1))."""
    if vec is None:
        vec = {}
    for a in word:
        p = abs(a) - 1
        d = ACT[c][p]
        if a > 0:
            g = GEN.get((c, p))
            if g is not None:
                vec[g] = vec.get(g, 0) + 1
        else:
            g = GEN.get((d, p))
            if g is not None:
                vec[g] = vec.get(g, 0) - 1
        c = d
    return c, vec


def build_h1():
    rels = [(u, v) for u, v in P.check_presentation()]
    rels.append((P.delta2_pure(), ()))
    rows = []
    for u, v in rels:
        w = tuple(u) + P.finv(v)
        for c in range(len(ACT)):
            d, vec = trace(w, c)
            assert d == c
            vec = {g: a for g, a in vec.items() if a}
            if vec:
                rows.append(vec)
    ngen = len(GEN)
    ident = [{g: 1} for g in range(ngen)]
    cols, R, E = C.unit_eliminate(ngen, rows, ident)
    n = len(cols)
    Rd = sorted({tuple(r) for r in C.to_dense(R, cols)})
    H = C.hnf_rows([list(r) for r in Rd], n)
    Ed = np.array(C.to_dense(E, cols), dtype=object)
    return ngen, n, H, Ed


class H1:
    def __init__(self):
        t0 = time.time()
        self.ngen, self.n, self.H, self.E = build_h1()
        self.rank, self.tors = C.h1_invariants(self.H, self.n)
        self.time = time.time() - t0

    def cls(self, word, c=0):
        d, vec = trace(word, c)
        x = np.zeros(self.n, dtype=object)
        for g, a in vec.items():
            x = x + a * self.E[g]
        return d, C.reduce_mod_hnf([int(t) for t in x], self.H)

    def is_zero(self, word):
        d, r = self.cls(word)
        assert d == 0, "word not in K4"
        return not any(r)


def conj(h, w):
    return P.fred(tuple(h) + tuple(w) + P.finv(h))


def random_pure(rng, length):
    return P.fred(tuple(rng.choice([1, -1]) * rng.randint(1, NP)
                        for _ in range(length)))


def main(out, trials=200, seed=7):
    rng = random.Random(seed)
    h1 = H1()
    res = {"cosets": len(ACT), "schreier_gens": h1.ngen,
           "h1_rank": h1.rank, "h1_torsion": h1.tors,
           "reduced_gens": h1.n}
    print(res, f"[{h1.time:.1f}s]", flush=True)
    tab = P.conj_table()
    TW = P.standard_twists(tab)
    tri = list(TW)
    # --- the 160 separating classes (conjugates of T_A^2 by the 512 cosets)
    classes = {}
    over = {}
    for t in tri:
        sq = TW[t] * 2
        for c in range(len(ACT)):
            d, r = h1.cls(conj(REP[c], sq))
            assert d == 0
            classes.setdefault(r, t)
    keys = sorted(classes)
    for k in keys:
        over.setdefault(classes[k], []).append(k)
    res["classes"] = len(keys)
    res["classes_per_splitting"] = sorted({len(v) for v in over.values()})
    B = C.w_lattice(h1.H, [list(k) for k in keys], h1.n)
    from math import gcd
    g = 0
    for r in B:
        g = gcd(g, sum(r))
    res["W_rank"], res["gcd_aug"] = len(B), g
    print({k: res[k] for k in ("classes", "classes_per_splitting", "W_rank",
                               "gcd_aug")}, flush=True)

    def palindrome(factors):
        x = ()
        for f in factors:
            x = x + f
        xr = ()
        for f in reversed(factors):
            xr = xr + f
        return P.fred(x + xr)

    def trial(kind):
        order = tri[:]
        rng.shuffle(order)
        if kind == "repeat":          # one splitting twice, one missing
            order[0] = order[1]
        if kind == "nine":
            order = order[:9]
        hs = [random_pure(rng, rng.randint(0, 12)) for _ in order]
        if kind == "standard":
            hs = [() for _ in order]
        factors = [conj(h, TW[t]) for h, t in zip(hs, order)]
        if kind == "control":         # random transversal product
            w = ()
            for h, t in zip(hs, order):
                g2 = random_pure(rng, rng.randint(0, 12))
                w = w + conj(g2, conj(h, TW[t] * 2))
            return h1.is_zero(P.fred(w))
        if kind == "nine":
            w = palindrome(factors)
            d, r = h1.cls(w)
            return d == 0 and not any(r)
        return h1.is_zero(palindrome(factors))

    for kind in ("standard", "random-curves", "repeat", "nine", "control"):
        t0 = time.time()
        hits = sum(trial(kind) for _ in range(trials))
        res[f"{kind}_zero"] = f"{hits}/{trials}"
        print(kind, hits, "/", trials, f"[{time.time()-t0:.1f}s]", flush=True)
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out)
    return res, h1, TW


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else
         os.path.join(HERE, "palindrome-results.json"))
