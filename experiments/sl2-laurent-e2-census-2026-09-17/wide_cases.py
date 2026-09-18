"""Reruns of level-5 linear Cohn matrices with wide slacks (width slack >= 3, large l1 slack).

Motivated by C(6, 3+t) and C(6, 2+t): the width-slack-2 pruned space is exhausted and the
first width-slack-3 run then succeeds a few states later (hard_cases.py output in
results.txt).  Usage: python3 wide_cases.py budget n:c0,c1,... ; prints
(n, f, slack, (reduced?, steps, best key), seconds).  A False is evidence only.
"""
import sys
import time

from mreduce import cohn, mk, reduce_matrix

SLACKS = [(3, 300), (5, 300), (8, 400)]

if __name__ == "__main__":
    budget = int(sys.argv[1])
    for spec in sys.argv[2:]:
        n, f = spec.split(":")
        n = int(n)
        f = tuple(int(x) for x in f.split(","))
        for slack in SLACKS:
            t0 = time.time()
            r = reduce_matrix(cohn(mk((n,)), mk(f)), budget, slack)
            print(n, f, slack, r, round(time.time() - t0, 1), flush=True)
