#!/usr/bin/env python3
"""Falsifiable test of the staircase law for the first stubborn layer.

For the staircase sets  S(m,d) = X_m X_(m+1) ... X_(m+d-1)  (normal-form monomials
x_(i_1)...x_(i_d) with i_1 <= ... <= i_d and i_t <= m+t-1) the computed first stubborn layer
a_min(m,d) satisfies, on every case computed so far,

        2 a_min(m, d) + 1  =  3^(d-1) (2m + 1).

Data behind the prediction: d=1 gives a_min = m for m = 1..6 (PROVED by the two-block construction
of thompson-f-generator-sets-admit-no-private-pivot-order); d=2 gives 1, 4, 7, 10 for m = 0..3;
d=3 gives 4 at m=0.  Note S(0,d) = x_0 . S(1,d-1) and a common left factor does not change the
bipartite structure (thompson-f-stubborn-sets-split-off-the-tail, item 5), so a_min(0,d) =
a_min(1,d-1), which the law already encodes.

Each case is tested at BOTH a = a_min - 1 (must be empty) and a = a_min (must be nonempty).

Run:  python3 law_test.py ./prefix_core [m,d m,d ...]
Default cases: (1,3) and (0,4), both predicting a_min = 13, the first genuinely new value.
"""
import json
import subprocess
import sys

BIN = sys.argv[1] if len(sys.argv) > 1 else "./prefix_core"
CASES = [tuple(int(x) for x in arg.split(",")) for arg in sys.argv[2:]] or [(1, 3), (0, 4)]


def XX(m, d):
    out = [()]
    for t in range(d):
        out = [p + (i,) for p in out for i in range((p[-1] if p else 0), m + t + 1)]
    return out


def spec(S):
    return ";".join(",".join(map(str, s)) for s in S)


for (m, d) in CASES:
    S = XX(m, d)
    pred = (3 ** (d - 1) * (2 * m + 1) - 1) // 2
    for a in (pred - 1, pred):
        out = subprocess.run([BIN, str(a), spec(S)], capture_output=True, text=True)
        rec = {"m": m, "d": d, "|S|": len(S), "predicted_a_min": pred,
               "expected": "empty" if a < pred else "nonempty"}
        try:
            rec.update(json.loads(out.stdout))
        except Exception:
            rec["error"] = out.stderr[:300]
        rec["law_holds_here"] = (rec.get("core", -1) == 0) == (a < pred)
        print(json.dumps(rec), flush=True)
