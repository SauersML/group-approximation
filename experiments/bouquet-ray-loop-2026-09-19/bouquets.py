#!/usr/bin/env python3
"""The 472 linear bouquet recursions of `same-point-loop-recursions-reduce-to-loop-graph-words`,
in the Nielsen basis {a, e, S = l_s = A s B, T = l_t = C t D}, with fast level-n permutations.

Library for node `linear-bouquet-recursions-ray-loop-and-contraction`.  Points 0..10.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "loop-graph-screen-2026-09-18"))
import numpy as np
from loopgraph import N, ID, reduce, inv, fmt, pmul, pinv, W
from same_point_screen import family, check_L1, classify_components

def bouquets():
    """yield (name, R, info) for the linear bouquet class (Gamma_1 of rank 2)."""
    for name, R in family(True):
        ok, loops = check_L1(R)
        comps = classify_components(R, loops)
        if max([rk for _, rk, _, _ in comps] + [0]) < 2: continue
        (xs, A, B), (xt, C, D) = loops["s"], loops["t"]
        S = A + (("s", 1),) + B; T = C + (("t", 1),) + D
        z = pinv(R.perm(A))[xs]
        assert z == pinv(R.perm(C))[xt] == R.perm(((("s", 1),) + B))[xs] == R.perm((("t", 1),) + D)[xt]
        yield name, R, dict(S=S, T=T, z=z, sigma=R.perm(S), tau=R.perm(T))

class Levels:
    """permutations of every letter on X^n (index = base-11 number, first letter most
    significant), computed recursively; right actions, p_{uv} = p_v[p_u]."""
    def __init__(self, R, n):
        self.R, self.n = R, n
        self.P = {0: {}}
        letters = list(R.rooted) + list(R.states)
        for k in range(1, n + 1):
            M = N ** (k - 1); self.P[k] = {}
            for l in letters:
                p = np.empty(N * M, dtype=np.int64)
                root = R.lperm(l, 1)
                for x in range(N):
                    sec = R.lsec(l, 1, x)
                    q = self.word(sec, k - 1)
                    p[x * M:(x + 1) * M] = root[x] * M + q
                self.P[k][l] = p
    def word(self, w, k):
        M = N ** k
        p = np.arange(M, dtype=np.int64)
        if k == 0: return p
        for l, e in w:
            q = self.P[k][l]
            if e == -1:
                qi = np.empty_like(q); qi[q] = np.arange(M); q = qi
            p = q[p]
        return p

def cycles_str(p):
    """GAP cycle notation of a 0-based permutation array (points shifted by 1)"""
    seen = np.zeros(len(p), bool); out = []
    for i in range(len(p)):
        if seen[i] or p[i] == i: seen[i] = True; continue
        c = []; j = i
        while not seen[j]: seen[j] = True; c.append(j + 1); j = p[j]
        out.append("(" + ",".join(map(str, c)) + ")")
    return "".join(out) or "()"
