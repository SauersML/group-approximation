#!/usr/bin/env python3
"""Cross-checks for doubling_flow on tiny universes.

1. Brute force: the minimum of |S Y| / |Y| over all nonempty Y in M_{D,L} (exhaustive subsets)
   must equal the flow program's exact value.
2. Inert-letter lemma: Lambda_S(D) = lambda*_S(D, R(D)) with R(D) = max_t (s_t + D + d - t);
   so lambda*_S(D, L) must be constant for L >= R(D).
"""
import itertools, json, subprocess, sys
from fractions import Fraction

def lml(j, w):
    out = []; k = 0
    while k < len(w) and w[k] < j:
        out.append(w[k]); j += 1; k += 1
    return tuple(out + [j] + list(w[k:]))

def mul(a, b):
    r = tuple(b)
    for j in reversed(a):
        r = lml(j, r)
    return r

SPECS = {
    "X1": "0;1", "X2": "0;1;2", "S21": "0,0;0,1;0,2;1,1;1,2",
    "S22": "0,0;0,1;0,2;0,3;1,1;1,2;1,3;2,2;2,3",
}

def parse(spec):
    return [tuple(int(x) for x in m.split(",")) for m in spec.split(";")]

def flow(D, L, spec):
    out = subprocess.run(["./doubling_flow", str(D), str(L), spec], capture_output=True, text=True, check=True).stdout
    r = json.loads(out)
    return Fraction(r["min_ratio_num"], r["min_ratio_den"])

def brute(D, L, S):
    U = list(itertools.combinations_with_replacement(range(L + 1), D))
    img = [set(mul(s, u) for s in S) for u in U]
    best = None
    for mask in range(1, 1 << len(U)):
        tot = set(); n = 0
        for i in range(len(U)):
            if mask >> i & 1:
                tot |= img[i]; n += 1
        r = Fraction(len(tot), n)
        if best is None or r < best:
            best = r
    return best, len(U)

def R(S, D):
    d = len(S[0])
    return max(s[t] + D + d - 1 - t for s in S for t in range(d))

ok = True
for name in ["X1", "X2", "S21", "S22"]:
    S = parse(SPECS[name])
    for D, L in [(1, 2), (1, 4), (2, 2), (2, 3), (3, 2), (2, 4)]:
        if len(list(itertools.combinations_with_replacement(range(L + 1), D))) > 16:
            continue
        b, n = brute(D, L, S); f = flow(D, L, SPECS[name])
        print("brute", name, D, L, n, b, f, b == f); ok &= (b == f)
for name in ["X1", "X2", "S21", "S22"]:
    S = parse(SPECS[name])
    for D in range(1, 7):
        r = R(S, D)
        vals = [flow(D, L, SPECS[name]) for L in range(r, r + 5)]
        below = flow(D, r - 1, SPECS[name])
        const = all(v == vals[0] for v in vals)
        print("lemma", name, D, "R=%d" % r, "at R-1:", below, "R..R+4:", [str(v) for v in vals], const)
        ok &= const
print("ALL_OK", ok)
