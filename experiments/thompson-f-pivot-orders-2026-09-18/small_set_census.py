#!/usr/bin/env python3
"""Exhaustive census: does EVERY finite monomial set of the positive monoid of F have a stubborn
layer, i.e. does the private-pivot (triangular doubling) certificate die for all of them?

For each S below we compute the least `a` with `core(P_a(S)) != 0`, which by
`thompson-f-stubborn-sets-split-off-the-tail` is the least degree carrying a stubborn set, and which
by `thompson-f-p22-monomials-admit-no-private-pivot-order`, item 1, kills every private pivot order
for S.  Sets with |S| = 1 are skipped: the single successor of every point is private, so P_0 is
already stubborn and a_min = 0 trivially.

Groups:
  `letters2`  all 57 subsets of size >= 2 of the six degree-2 monomials with letters <= 2
  `letters3`  all 1013 subsets of size >= 2 of the ten degree-2 monomials with letters <= 3
  `deg3`      selected degree-3 sets
It also records `(2 a_min + 1) mod 3^(d-1)`, to test whether the divisibility in the staircase law
of `thompson-f-staircase-sets-have-stubborn-layers` is an invariant of all sets (it is not).

Run:  python3 small_set_census.py ./prefix_core [group] [max |P_a|] [amax]
"""
import itertools
import json
import subprocess
import sys
from math import comb

BIN = sys.argv[1] if len(sys.argv) > 1 else "./prefix_core"
GROUP = sys.argv[2] if len(sys.argv) > 2 else "letters2"
BUDGET = int(sys.argv[3]) if len(sys.argv) > 3 else 2_000_000
AMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 14


def f(n, r):
    return 0 if n < r else (1 if r == 0 and n == 0 else r * comb(2 * n - r - 1, n - 1) // n)


def K_of(S):
    return max(s[t] + len(s) - t + 1 for s in S for t in range(len(s)))


def spec(S):
    return ";".join(",".join(map(str, s)) for s in S)


def a_min(S):
    K = K_of(S)
    for a in range(1, AMAX + 1):
        if f(K + a, K) > BUDGET:
            return None, a - 1
        out = subprocess.run([BIN, str(a), spec(S)], capture_output=True, text=True)
        if out.returncode != 0:
            return None, a - 1
        if json.loads(out.stdout)["core"] > 0:
            return a, a
    return None, AMAX


def subsets(mons):
    for k in range(2, len(mons) + 1):
        for S in itertools.combinations(mons, k):
            yield list(S)


GROUPS = {
    "letters2": list(subsets([(i, j) for i in range(3) for j in range(i, 3)])),
    "letters3": list(subsets([(i, j) for i in range(4) for j in range(i, 4)])),
    "deg3": [[(0, 0, 0), (1, 1, 1)], [(0, 0, 0), (0, 1, 2), (1, 1, 1)],
             [(0, 0, 0), (1, 1, 1), (2, 2, 2)], [(0, 0, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1)],
             [(0, 1, 2), (1, 2, 3)], [(0, 0, 2), (1, 1, 3)]],
}

found = unresolved = viol = 0
for S in GROUPS[GROUP]:
    d = len(S[0])
    a, reached = a_min(S)
    rec = {"S": spec(S), "|S|": len(S), "d": d, "K": K_of(S), "a_min": a, "searched_to": reached}
    if a is None:
        unresolved += 1
    else:
        found += 1
        rec["(2a+1) mod 3^(d-1)"] = (2 * a + 1) % 3 ** (d - 1)
        viol += 1 if rec["(2a+1) mod 3^(d-1)"] else 0
    print(json.dumps(rec), flush=True)
print(json.dumps({"group": GROUP, "sets": len(GROUPS[GROUP]), "a_min_found": found,
                  "unresolved_within_budget": unresolved, "no_stubborn_layer_proved": 0,
                  "divisibility_violations": viol}))
