#!/usr/bin/env python3
"""Fox matrix of a permutation representation twisted by t^chi, evaluated at
t0 in GF(p^k).  Phi(x) = P_x t^chi(x) is monomial, so every Fox block is a
sum of +-t0^n placed at positions (sigma(y), y)."""
import numpy as np
from twisted_alexander import RELS, CHI


def fox_blocks(perms_g):
    """perms_g: 4 permutations (numpy arrays).  Returns for each relator j and
    generator i a list of (sign, power, perm) terms."""
    n = len(perms_g[0])
    invs = [np.argsort(g) for g in perms_g]
    ident = np.arange(n)
    terms = {}
    for j, r in enumerate(RELS):
        pref = ident.copy()
        pw = 0
        for (g, e) in r:
            if e == 1:
                terms.setdefault((j, g), []).append((1, pw, pref.copy()))
                pref = pref[perms_g[g]]
                pw += CHI[g]
            else:
                pref = pref[invs[g]]
                pw -= CHI[g]
                terms.setdefault((j, g), []).append((-1, pw, pref.copy()))
        assert np.array_equal(pref, ident) and pw == 0, "relator fails"
    return terms


def perm_matrix_positions(pref):
    # matrix of composite permutation pref: column y has a 1 in row pref[y]
    # (P_a P_b = P_{a o b} with P_s e_y = e_{s(y)}); prefix product in fox is
    # P_{y1} P_{y2}... = P_{y1 o y2 o ...}; pref = pref[g] implements pref o g.
    return pref


def fox_matrix_gfq(F, perms_g, t0):
    n = len(perms_g[0])
    terms = fox_blocks(perms_g)
    # powers of t0 in GF(q)
    lt = int(F.log[t0])
    def tpow(m):
        return int(F.exp[(lt * m) % (F.q - 1)])
    J = np.zeros((6 * n, 4 * n), dtype=np.int64)
    one = 1
    minus_one = int(F.neg(np.array([1]))[0])
    for (j, g), lst in terms.items():
        for (s, pw, pref) in lst:
            val = tpow(pw)
            if s == -1:
                val = int(F.mul(val, minus_one))
            rows = j * n + pref
            cols = g * n + np.arange(n)
            J[rows, cols] = F.add(J[rows, cols], np.full(n, val))
    return J


def defect_gfq(F, perms_g, rng, trials=2):
    n = len(perms_g[0])
    best = -1
    for _ in range(trials):
        t0 = rng.randrange(2, F.q)
        best = max(best, F.rank(fox_matrix_gfq(F, perms_g, t0)))
    return best, 3 * n


def coeff_matrix(regs):
    d = len(regs[0])
    terms = fox_blocks(regs)
    C = {}
    for (j, g), lst in terms.items():
        for (s, pw, pref) in lst:
            for y in range(d):
                key = (j * d + int(pref[y]), g * d + y)
                C.setdefault(key, {})
                C[key][pw] = C[key].get(pw, 0) + s
    return C, d


def evaluate(F, C, d, t0):
    J = np.zeros((6 * d, 4 * d), dtype=np.int64)
    for (r, c), poly in C.items():
        if not hasattr(F, 'add'):
            v = sum(co * F.pow(t0, m) for m, co in poly.items()) % F.p
        else:
            v = 0
            for m, co in poly.items():
                co %= F.p
                if co:
                    v = int(F.add[v, F.mul[co, F.pow(t0, m)]])
        J[r, c] = v
    return J


