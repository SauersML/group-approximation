"""Pointwise (almost sure) rules forced on relative-level laws by monotone pairs.

Monotone pair: words s, t and middle positions i != j with
    p_j(s) ⊇ p_j(t)  and  p_i(s) ⊆ p_i(t),   at least one inclusion strict.
The observable  omega_ji = (position j versus position i: below < tie with ratio C_j/C_i < above)
is then pointwise >= for s than for t, in every relative model (any levels, any positive weights,
any finer tie-breaking), and equal laws force equality almost surely.  For leaf sets
Y = p_j(s) ⊇ Y' = p_j(t) and X = p_i(s) ⊆ X' = p_i(t) this is the rule

    omega(H over Y, H over X) == omega(H over Y', H over X')    (pointwise, ties with weights).

We list the pairs and count the level functions in {1..L}^n (weights 1 and a generic weight
vector) that satisfy every rule.
Usage: python3 relative_rules.py m d L
"""
import itertools
import sys

import numpy as np

from relative_level_lp import setup


def monotone_pairs(L):
    ns, k = len(L), len(L[0])
    out = []
    for s, t in itertools.permutations(range(ns), 2):
        for i, j in itertools.permutations(range(k), 2):
            Ys, Yt = set(L[s][j]), set(L[t][j])
            Xs, Xt = set(L[s][i]), set(L[t][i])
            if Ys >= Yt and Xs <= Xt and (Ys > Yt or Xs < Xt):
                out.append((s, t, i, j))
    return out


def omega(Lv, Wv, Y, X):
    """Encode the comparison of the pieces with leaf sets Y and X: -1 below, +inf above,
    and on ties the ratio C_Y / C_X (as a float, weights generic)."""
    hy = Lv[:, list(Y)].max(axis=1)
    hx = Lv[:, list(X)].max(axis=1)
    cy = np.where(Lv[:, list(Y)] == hy[:, None], Wv[:, list(Y)], 0).sum(axis=1)
    cx = np.where(Lv[:, list(X)] == hx[:, None], Wv[:, list(X)], 0).sum(axis=1)
    return np.where(hy < hx, -1.0, np.where(hy > hx, np.inf, cy / np.maximum(cx, 1e-300)))


def survivors(m, d, Lmax, weights="generic"):
    S, LV, L = setup(m, d)
    n = len(LV)
    pairs = monotone_pairs(L)
    Lv = np.array([lev for lev in itertools.product(range(1, Lmax + 1), repeat=n) if min(lev) == 1])
    if weights == "generic":
        Wv = np.tile(np.array([1.0 + np.sqrt(p) for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)[:n]]),
                     (len(Lv), 1))
    else:
        Wv = np.ones_like(Lv, dtype=float)
    ok = np.ones(len(Lv), bool)
    for s, t, i, j in pairs:
        ok &= omega(Lv, Wv, L[s][j], L[s][i]) == omega(Lv, Wv, L[t][j], L[t][i])
    return S, L, pairs, Lv[ok]


if __name__ == "__main__":
    m, d, Lmax = map(int, sys.argv[1:4])
    for wmode in ("generic", "ones"):
        S, L, pairs, surv = survivors(m, d, Lmax, wmode)
        print(f"(m,d)=({m},{d}) L={Lmax} weights={wmode}: monotone pairs={len(pairs)} "
              f"survivors={len(surv)} of {Lmax ** len(L[0][0]) if False else 'all'}")
        for lev in surv[:40]:
            print("   ", "".join(map(str, lev)))
