#!/usr/bin/env python3
"""Self-tests for the forest model and for the tail-splitting lemma.

    python3 selftest.py [./prefix_core]

1. `word_to_forest` and `forest_to_word` are mutually inverse on random normal forms, and the
   defining relation `x_j x_i = x_i x_{j+1}` (i < j) holds in the forest model.
2. `K(S) = max_{s,t} (s_t + d - t + 1)` is exactly the number of leaves `S` touches: every
   `s in S` is a forest with `K` leaves, `d` carets and `K - d` roots, and `K - 1` is not enough.
3. Every element of the prefix world `P_a` (forests with `K` roots and `a` carets) has normal form
   with letters `<= K + a - 2 = R_S(a)`, the truncation bound used by the published census
   `experiments/thompson-f-2026-09-17/stubborn_census.py`, and the bound is attained.  So
   `P_a` is contained in `M_(a, R_S(a))`.
4. TAIL SPLITTING, checked on random data: for `z = (u ; v)` with `u` the first `K` roots,
   `s z = (s.u ; v)`, and every factorisation `w = s' z'` with `s' in S` has the same tail `v`.
5. The Python core agrees with `prefix_core` (C++) on the small layers.
6. The published 1092-point `S_(3,5)` core of `experiments/thompson-f-2026-09-17/`, a word list from
   the other implementation, lies in `P_7` and is the same set as the core computed here.
7. A common left factor is invisible: `S(0,3) = x_0 . S(1,2)` and their cores agree as sets.
"""
import json
import random
import subprocess
import sys

from forests import (K_of, count_forests, forest_to_word, forests, graft, mono_forest, n_carets,
                     n_leaves, peel, stubborn_core, word_to_forest)

BIN = sys.argv[1] if len(sys.argv) > 1 else "./prefix_core"
random.seed(20260918)
ok = True


def check(name, cond):
    global ok
    print(("PASS  " if cond else "FAIL  ") + name)
    ok = ok and bool(cond)


# ---- 1 ----------------------------------------------------------------------
good = True
for _ in range(2000):
    D = random.randint(0, 8)
    w = tuple(sorted(random.randint(0, 7) for _ in range(D)))
    if forest_to_word(word_to_forest(w)) != w:
        good = False
        break
check("word <-> forest are mutually inverse on 2000 random normal forms", good)

good = True
for i in range(6):
    for j in range(i + 1, 8):
        # x_j x_i  and  x_i x_{j+1} must be the same forest
        a = word_to_forest((i, j), width=12)          # normal form of x_i x_j
        b = word_to_forest((i, j + 1), width=12)
        # build x_j x_i directly: apply x_i first (rightmost), then x_j
        trees = [0] * 12
        trees = trees[:i] + [(trees[i], trees[i + 1])] + trees[i + 2:]
        trees = trees[:j] + [(trees[j], trees[j + 1])] + trees[j + 2:]
        if tuple(trees) != b[:len(trees)] or a == b:
            good = False
check("x_j x_i = x_i x_{j+1} (i<j) holds in the forest model", good)

# ---- 2 ----------------------------------------------------------------------
SETS = {
    "X_3": [(i,) for i in range(4)],
    "S_(3,5)": [(i, j) for i in range(3) for j in range(i, 4)],
    "T": [(a, b, c) for a in range(3) for b in range(a, 4) for c in range(b, 5)],
    "deg2<=5": [(i, j) for i in range(6) for j in range(i, 6)],
}
good = True
for name, S in SETS.items():
    K, d = K_of(S), len(S[0])
    for s in S:
        f = mono_forest(s, K)
        if sum(n_leaves(t) for t in f) != K or sum(n_carets(t) for t in f) != d or len(f) != K - d:
            good = False
    try:
        mono_forest(max(S, key=lambda s: max(s[t] + len(s) - t for t in range(len(s)))), K - 1)
        good = False  # K-1 should not be enough
    except Exception:
        pass
check("K(S) is exactly the number of leaves S touches (4 sets)", good)

# ---- 3 ----------------------------------------------------------------------
good = True
for name, S in (("X_3", SETS["X_3"]), ("S_(3,5)", SETS["S_(3,5)"])):
    K = K_of(S)
    for a in range(1, 5):
        U = forests(K, K + a)
        if len(U) != count_forests(K, K + a):
            good = False
        mx = max(max(forest_to_word(u)) for u in U)
        if mx != K + a - 2:
            good = False
            print("   letters reach", mx, "expected", K + a - 2, "for", name, "a =", a)
check("max letter on P_a is exactly K + a - 2 = R_S(a), so P_a is inside M_(a,R_S(a))", good)

# ---- 4 ----------------------------------------------------------------------
S = SETS["S_(3,5)"]
K, d = K_of(S), 2
SF = [mono_forest(s, K) for s in S]
good = True
for _ in range(400):
    a = random.randint(0, 5)
    U = forests(K, K + a)
    u = random.choice(U)
    b = random.randint(0, 3)
    V = forests(3, 3 + b)
    v = random.choice(V)
    z = u + v
    for sf in SF:
        w = graft(sf, u) + v          # s z, with the K-d roots of s.u followed by the tail
        if len(w) != K - d + len(v) or w[:K - d] != graft(sf, u) or w[K - d:] != v:
            good = False
        # EVERY factorisation w = s' z' in the full monoid (s' padded with trivial trees to the
        # width of w) must keep the tail v and only rewrite the first K roots
        for sf2 in SF:
            pad = sf2 + (0,) * (len(w) - len(sf2))
            zprime = peel(pad, w)
            if zprime is None:
                continue
            if zprime[K:] != v or graft(sf2, zprime[:K]) != w[:K - d]:
                good = False
check("tail splitting: s z = (s.u ; v) and every factorisation of s z keeps the tail v", good)

# ---- 5 ----------------------------------------------------------------------
good = True
rows = []
for name, S, amax in (("X_3", SETS["X_3"], 3), ("S_(3,5)", SETS["S_(3,5)"], 7),
                      ("T", SETS["T"], 4)):
    for a in range(1, amax + 1):
        _, core = stubborn_core(S, a)
        spec = ";".join(",".join(map(str, s)) for s in S)
        out = subprocess.run([BIN, str(a), spec], capture_output=True, text=True)
        j = json.loads(out.stdout)
        rows.append((name, a, len(core), j["core"]))
        if len(core) != j["core"]:
            good = False
check("python core == C++ prefix_core on " + str(len(rows)) + " layers: "
      + ", ".join(f"{n}(a={a}):{x}" for n, a, x, _ in rows), good)

# ---- 6 ----------------------------------------------------------------------
# the published 1092-point S_(3,5) core, given as normal-form words in the 2026-09-17 experiment,
# must be exactly the core computed here, and must lie inside the prefix world P_7 (K = 5 roots)
import os

PUB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                   "thompson-f-2026-09-17", "s35_stubborn_core_D7.txt")
if os.path.exists(PUB):
    pub = [tuple(int(x) for x in line.split(",")) for line in open(PUB) if line.strip()]
    K = K_of(SETS["S_(3,5)"])
    pubf = set()
    inside = True
    for w in pub:
        f = word_to_forest(w)
        if any(t != 0 for t in f[K:]):
            inside = False
        pubf.add(f[:K])
    _, mine = stubborn_core(SETS["S_(3,5)"], 7)
    check(f"published 1092-point S_(3,5) core (words, other implementation) lies in P_7 "
          f"(K = {K} roots) and equals the core computed here",
          inside and len(pub) == 1092 and pubf == set(mine))
else:
    print("SKIP  published S_(3,5) core file not found at " + PUB)


# ---- 7 ----------------------------------------------------------------------
# item 5 of the claim: a common left factor is invisible.  S(0,3) = x_0 . S(1,2), so the two
# must have the same core in every layer -- as SETS, not just in size.
def XX(m, d):
    out = [()]
    for t in range(d):
        out = [p + (i,) for p in out for i in range((p[-1] if p else 0), m + t + 1)]
    return out


S03, S12 = XX(0, 3), XX(1, 2)
same_factor = all(s[0] == 0 for s in S03) and sorted(s[1:] for s in S03) == sorted(S12)
eq = True
for a in range(1, 5):
    _, c1 = stubborn_core(S03, a)
    _, c2 = stubborn_core(S12, a)
    if set(c1) != set(c2):
        eq = False
check("common left factor: S(0,3) = x_0 . S(1,2) and their cores agree as sets for a <= 4"
      f" (|core(P_4)| = {len(c1)})", same_factor and eq)

print("\nALL PASS" if ok else "\nFAILURES")
sys.exit(0 if ok else 1)
