#!/usr/bin/env python3
"""Census of stubborn cores in the PREFIX WORLDS P_a(S) of the positive monoid of Thompson's F.

    g++ -O2 -std=c++17 -o prefix_core prefix_core.cpp
    python3 prefix_census.py ./prefix_core [group]        # group in: verify, survivors, all

`verify`    reproduces every published row of experiments/thompson-f-2026-09-17/stubborn_census.jsonl
            in the prefix model (an independent implementation: forests + graft/peel, against the
            old word rewriting), and checks the two-block sizes 2, 8, 40, 221, 1288, 7752 of
            `thompson-f-generator-sets-admit-no-private-pivot-order`.
`survivors` pushes the two sets that had NO stubborn layer in the published census
            (`T = {x_a x_b x_c : a<=2, b<=3, c<=4}` through D = 10, and all 21 degree-2
            monomials with letters <= 5 through D = 9) as deep as the budget allows.

Every line of output is JSON; `core > 0` in any layer means NO private-pivot order exists for S
(claim thompson-f-p22-monomials-admit-no-private-pivot-order, item 1), so that triangular
doubling certificate is dead for S.
"""
import json
import subprocess
import sys
from math import comb

BIN = sys.argv[1] if len(sys.argv) > 1 else "./prefix_core"
GROUP = sys.argv[2] if len(sys.argv) > 2 else "verify"
BUDGET = int(sys.argv[3]) if len(sys.argv) > 3 else 20_000_000


def spec(S):
    return ";".join(",".join(map(str, s)) for s in S)


def f(n, r):
    """ordered forests of r binary trees with n leaves"""
    if r == 0:
        return 1 if n == 0 else 0
    if n < r:
        return 0
    return r * comb(2 * n - r - 1, n - 1) // n


def K_of(S):
    return max(s[t] + len(s) - t + 1 for s in S for t in range(len(s)))


X = lambda m: [(i,) for i in range(m + 1)]

VERIFY = [
    ("X_1", X(1), 2), ("X_2", X(2), 3), ("X_3", X(3), 4), ("X_4", X(4), 5),
    ("X_5", X(5), 6), ("X_6", X(6), 7),
    ("S_(2,4)=X_1X_2", [(i, j) for i in range(2) for j in range(i, 3)], 5),
    ("S_(3,5)=X_2X_3", [(i, j) for i in range(3) for j in range(i, 4)], 8),
    ("S_(4,6)=X_3X_4", [(i, j) for i in range(4) for j in range(i, 5)], 11),
    ("squares{x0x0,x1x1,x2x2}", [(0, 0), (1, 1), (2, 2)], 5),
]

T_SET = [(a, b, c) for a in range(3) for b in range(a, 4) for c in range(b, 5)]
DEG2_5 = [(i, j) for i in range(6) for j in range(i, 6)]

SURVIVORS = [
    ("T={abc: a<=2,b<=3,c<=4}", T_SET, 15),
    ("all degree-2 letters<=5", DEG2_5, 14),
]


def XX(m, d):
    """X_m X_(m+1) ... X_(m+d-1) = the normal-form monomials x_{i_1}..x_{i_d} with
    i_1 <= ... <= i_d and i_t <= m + t - 1.  d=1 gives X_m, d=2 gives S_(m+1,m+3)."""
    out = [()]
    for t in range(d):
        out = [p + (i,) for p in out for i in range((p[-1] if p else 0), m + t + 1)]
    return out


# the first stubborn layer a_min(X_m..X_{m+d-1}) as a function of m, for each degree d:
# d = 1 gives a_min = m, d = 2 gives a_min = 3m+1 (both established/computed).  These rows
# extend the law to d = 3 and d = 4, which is what decides whether the surviving degree-3 set
# T = X_2 X_3 X_4 is genuinely order-certifiable or merely below its threshold.
FAMILY = [(f"X_{m}..X_{m + d - 1} (d={d})", XX(m, d), 30)
          for d in (2, 3, 4) for m in (0, 1, 2)]


def run(name, S, amax):
    K = K_of(S)
    for a in range(1, amax + 1):
        size = f(K + a, K)
        if size > BUDGET:
            print(json.dumps({"set": name, "stopped_before_a": a, "|P_a|": size}), flush=True)
            return
        out = subprocess.run([BIN, str(a), spec(S)], capture_output=True, text=True)
        if out.returncode not in (0,):
            print(json.dumps({"set": name, "a": a, "error": out.returncode,
                              "stdout": out.stdout, "stderr": out.stderr[:400]}), flush=True)
            return
        j = json.loads(out.stdout)
        j["set"] = name
        print(json.dumps(j), flush=True)
        if j["core"] > 0:
            return


if GROUP in ("verify", "all"):
    for name, S, amax in VERIFY:
        run(name, S, amax)
if GROUP in ("survivors", "all"):
    for name, S, amax in SURVIVORS:
        run(name, S, amax)
if GROUP in ("family", "all"):
    for name, S, amax in FAMILY:
        run(name, S, amax)
