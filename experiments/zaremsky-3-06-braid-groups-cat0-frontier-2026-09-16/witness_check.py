#!/usr/bin/env python3
"""Independent linear-algebra check of the n = 8 witness of
research/some-noncrossing-chain-defeats-all-pair-pivots.md (no code shared with nc_pairs.py).

Checks, over the reals with numpy ranks:
  1. f(K(P)) = f(P)^perp for <y, z> = sum_k s_k(y) z_k (Lemma D of the 2026-09-13 artifact), for
     P = {12,34,56,78} -> K(P) = {2468} and Q = {18,23,45,67} -> K(Q) = {1357}.
  2. For each of the 48 opposite universal pairs (v, w) (p, c), whether f(R) = (f(R) cap f(v)) + (f(R) cap f(w))
     for R in {P, Q, K(P), K(Q)}, compared with the cut criterion (every block of R missing p lies in A1 or A2).
  3. compat(P) and compat(Q) are disjoint; compat(K(P)) and compat(K(Q)) are disjoint.
  4. The III' pairs: {1256,34,78}, {3478,12,56} above P with crossing full join; {26}, {48} below K(P) with crossing
     full join.
Points are 1..8 in the output; p is 1-indexed.
"""
import itertools
import numpy as np

n = 8
def sub(blocks):
    """basis of f(x) = {y in R^n : sum y = 0 and sum over each block of x (singletons included) is 0}"""
    cov = set().union(*blocks)
    allb = [set(b) for b in blocks] + [{i} for i in range(1, n + 1) if i not in cov]
    A = np.array([[1.0 if i in b else 0.0 for i in range(1, n + 1)] for b in allb])
    u, s, vt = np.linalg.svd(A)
    r = int((s > 1e-9).sum())
    return vt[r:]                       # null space rows

def rank(M):
    return 0 if M.size == 0 else np.linalg.matrix_rank(M, tol=1e-9)

def dim_int(A, B):
    if len(A) == 0 or len(B) == 0:
        return 0
    return len(A) + len(B) - rank(np.vstack([A, B]))

def parse(s):
    return [set(int(ch) for ch in blk) for blk in s.split(",")] if s else []

P, Q, KP, KQ = parse("12,34,56,78"), parse("18,23,45,67"), parse("2468"), parse("1357")

# 1. Kreweras = orthogonality
G = np.array([[sum(1.0 for k in range(1, n + 1) if k >= j and k < i) for i in range(1, n + 1)] for j in range(1, n + 1)])
# <y, z> = sum_k s_k(y) z_k with s_k(y) = y_1 + ... + y_k: bilinear form y^T M z, M[j, i] = 1 if j <= i
M = np.array([[1.0 if j <= i else 0.0 for i in range(n)] for j in range(n)])
for X, KX, name in ((P, KP, "P"), (Q, KQ, "Q")):
    FX, FK = sub(X), sub(KX)
    print("dim f(%s) = %d, dim f(K%s) = %d, max |<f(%s), f(K%s)>| = %.2e" % (
        name, len(FX), name, len(FK), name, name, np.abs(FX @ M @ FK.T).max()))

# 2. cut criterion vs apartment splitting
def arcs(p, c):
    A1 = {(p - 1 + t) % n + 1 for t in range(1, c + 1)}
    A2 = {(p - 1 + t) % n + 1 for t in range(c + 1, n)}
    return A1, A2

def split_la(R, p, c):
    A1, A2 = arcs(p, c)
    FR, Fv, Fw = sub(R), sub([A1 | {p}]), sub([A2 | {p}])
    return dim_int(FR, Fv) + dim_int(FR, Fw) == len(FR)

def split_cut(R, p, c):
    A1, A2 = arcs(p, c)
    return all(p in b or b <= A1 or b <= A2 for b in R)

pairs = [(p, c) for p in range(1, n + 1) for c in range(1, n - 1)]
compat = {}
for R, name in ((P, "P"), (Q, "Q"), (KP, "KP"), (KQ, "KQ")):
    la = {pc for pc in pairs if split_la(R, *pc)}
    cut = {pc for pc in pairs if split_cut(R, *pc)}
    assert la == cut, name
    compat[name] = la
    print("compat(%s): %d pairs, linear algebra == cut criterion" % (name, len(la)),
          "| p + c even for all:", all((p + c) % 2 == 0 for p, c in la),
          "| p + c odd for all:", all((p + c) % 2 == 1 for p, c in la),
          "| p even for all:", all(p % 2 == 0 for p, c in la), "| p odd for all:", all(p % 2 == 1 for p, c in la))
print("compat(P) & compat(Q) =", compat["P"] & compat["Q"], "| compat(KP) & compat(KQ) =", compat["KP"] & compat["KQ"])

# 4. III' pairs: full join crossing
def crossing(blocks):
    for b1, b2 in itertools.permutations(blocks, 2):
        for a, c in itertools.combinations(sorted(b1), 2):
            inside = {t for t in b2 if a < t < c}
            if inside and (b2 - inside):
                return True
    return False

def full_join(x, y):
    bl = [set(b) for b in x + y]
    merged = True
    while merged:
        merged = False
        for i, j in itertools.combinations(range(len(bl)), 2):
            if bl[i] & bl[j]:
                bl[i] |= bl.pop(j); merged = True; break
    return bl

for x, y in ((parse("1256,34,78"), parse("3478,12,56")), (parse("26"), parse("48"))):
    J = full_join(x, y)
    print("x =", x, "y =", y, "| x, y noncrossing:", not crossing(x), not crossing(y), "| full join", J, "crossing:", crossing(J),
          "| f(x)+f(y) dim", rank(np.vstack([sub(x), sub(y)])), "= dim f(join)", len(sub(J)))
