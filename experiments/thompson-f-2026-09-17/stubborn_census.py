#!/usr/bin/env python3
"""Census of maximal stubborn subsets of M_(D, R_S(D)) for several monomial sets S of F.

Build:  g++ -O2 -std=c++17 -o stubborn_core stubborn_core.cpp
Run:    python3 stubborn_census.py ./stubborn_core > stubborn_census.jsonl
For each S, D increases until the maximal stubborn subset is nonempty or |M_(D,R)| > 2.5e6.
Then: python3 verify_stubborn_core.py s35_stubborn_core_D7.txt  (independent PL-map check).
"""
import json, math, subprocess, sys

BIN = sys.argv[1] if len(sys.argv) > 1 else "./stubborn_core"


def spec(S):
    return ";".join(",".join(map(str, s)) for s in S)


def R(S, D):
    return max(s[t] + D + len(s) - (t + 1) for s in S for t in range(len(s)))


SETS = [
    ("X_1", [(i,) for i in range(2)]),
    ("X_2", [(i,) for i in range(3)]),
    ("X_3", [(i,) for i in range(4)]),
    ("X_4", [(i,) for i in range(5)]),
    ("X_5", [(i,) for i in range(6)]),
    ("X_6", [(i,) for i in range(7)]),
    ("S_(2,4)=X_1X_2", [(i, j) for i in range(2) for j in range(i, 3)]),
    ("S_(3,5)=X_2X_3", [(i, j) for i in range(3) for j in range(i, 4)]),
    ("S_(4,6)=X_3X_4", [(i, j) for i in range(4) for j in range(i, 5)]),
    ("squares{x0x0,x1x1,x2x2}", [(0, 0), (1, 1), (2, 2)]),
    ("T={abc: a<=2,b<=3,c<=4}", [(a, b, c) for a in range(3) for b in range(a, 4) for c in range(b, 5)]),
    ("all degree-2 letters<=5", [(i, j) for i in range(6) for j in range(i, 6)]),
]

for name, S in SETS:
    for D in range(1, 13):
        L = R(S, D)
        if math.comb(L + D, D) > 2_500_000:
            print(json.dumps({"set": name, "stopped_before_D": D}), flush=True)
            break
        out = subprocess.run([BIN, str(D), str(L), spec(S)], capture_output=True, text=True, check=True).stdout
        j = json.loads(out)
        j["set"] = name
        print(json.dumps(j), flush=True)
        if j["core"] > 0:
            break
