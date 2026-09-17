#!/usr/bin/env python3
"""Brute-force check of the twisted linear profile construction.

Artifact: research/artifacts/twisted-linear-entropy-profiles-2026-09-17.md, Sections 1-2.

G = Z acting on K = F_4 by Frobenius (sigma_g(a) = a^(2^g)). Sites 0..N-1 carry
independent uniform X_g in F_4 (k = 1). The twisted codewords are
    Y_g = sigma_g(c0) X_g + sigma_g(c1) X_(g+1).
Enumerating all 4^N inputs, it checks:
  (a) every Shannon entropy (base 4) of a family of variables equals the F_4-rank of the
      corresponding functionals, so finite restrictions are entropic;
  (b) the entropy function is translation invariant, although the codewords use different
      coefficients at different sites: the profile is invariant, the code is not equivariant;
  (c) I(X_1 ; Y_F) = dim(site-1 layer ∩ span Y_F), and it does not exceed H(Y_1) here
      (F_4 ⋊ Z is amenable, so no deficit is possible).
Pure Python, no dependencies. Exit code 0 iff all checks pass.
"""
import itertools
import math
from collections import Counter

# GF(4) = {0, 1, w, w^2} encoded 0, 1, 2, 3; addition is xor, w^2 = w + 1.
_LOG = {1: 0, 2: 1, 3: 2}
_EXP = [1, 2, 3]
_INV = {1: 1, 2: 3, 3: 2}


def gmul(a, b):
    if a == 0 or b == 0:
        return 0
    return _EXP[(_LOG[a] + _LOG[b]) % 3]


def frob(a, g):
    # sigma_g = Frobenius^g; Frobenius has order 2 on F_4
    if g % 2:
        a = gmul(a, a)
    return a


N = 6
C0, C1 = 2, 1  # c0 = w, c1 = 1


def functional(var):
    kind, g = var
    v = [0] * N
    if kind == "X":
        v[g] = 1
    else:
        v[g] = frob(C0, g)
        v[g + 1] = frob(C1, g)
    return v


def rank_f4(rows):
    rows = [list(r) for r in rows]
    rk, col = 0, 0
    while rk < len(rows) and col < N:
        piv = next((i for i in range(rk, len(rows)) if rows[i][col]), None)
        if piv is None:
            col += 1
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        s = _INV[rows[rk][col]]
        rows[rk] = [gmul(s, x) for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col]:
                f = rows[i][col]
                rows[i] = [x ^ gmul(f, y) for x, y in zip(rows[i], rows[rk])]
        rk += 1
        col += 1
    return rk


def dot(v, x):
    s = 0
    for a, b in zip(v, x):
        s ^= gmul(a, b)
    return s


INPUTS = list(itertools.product(range(4), repeat=N))


def entropy4(vars_):
    funcs = [functional(v) for v in vars_]
    cnt = Counter(tuple(dot(f, x) for f in funcs) for x in INPUTS)
    tot = len(INPUTS)
    return -sum(c / tot * math.log(c / tot, 4) for c in cnt.values())


def main():
    ok = True
    variables = [("X", g) for g in range(N)] + [("Y", g) for g in range(N - 1)]
    cache = {}

    def h(fam):
        key = tuple(sorted(fam))
        if key not in cache:
            cache[key] = entropy4(list(key))
        return cache[key]

    oka = True
    for r in range(1, 4):
        for fam in itertools.combinations(variables, r):
            rk = rank_f4([functional(v) for v in fam])
            if abs(h(fam) - rk) > 1e-9:
                oka = False
                print("entropy/rank mismatch", fam, h(fam), rk)
    print("(a) entropy = F_4-rank on all families of size <= 3:", oka)
    ok = ok and oka

    okb = True
    for r in range(1, 4):
        for fam in itertools.combinations(variables, r):
            shifted = [(k, g + 1) for k, g in fam]
            if any((k == "X" and g >= N) or (k == "Y" and g >= N - 1) for k, g in shifted):
                continue
            if abs(h(fam) - h(shifted)) > 1e-9:
                okb = False
                print("not invariant", fam)
    print("(b) translation invariance of the profile:", okb)
    ok = ok and okb

    xs = [("X", 1)]
    yf = [("Y", g) for g in range(0, N - 1)]
    info = h(xs) + h(yf) - h(xs + yf)
    cap = 1 + rank_f4([functional(v) for v in yf]) - rank_f4([functional(v) for v in xs + yf])
    hy1 = h([("Y", 1)])
    print("(c) I(X_1;Y_F) = %.6f, dim(layer ∩ span Y_F) = %d, H(Y_1) = %.6f" % (info, cap, hy1))
    okc = abs(info - cap) < 1e-9 and info <= hy1 + 1e-9
    print("(c) dictionary identity and domination:", okc)
    ok = ok and okc
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
