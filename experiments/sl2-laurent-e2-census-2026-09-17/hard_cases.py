"""Larger-budget reruns of level-census budget failures with several slack settings.

Usage: python3 hard_cases.py budget n:c0,c1,... [n:c0,c1,...] ...
  e.g. python3 hard_cases.py 120000 3:1,1,2 2:1,1,0,1
Each argument n:coeffs means Cohn(n, f) with f = c0 + c1 t + ... .
Prints (n, f, slack, (reduced?, steps, best key), seconds).  A False is a search
failure, never a proof of non-elementarity.
"""
import sys
import time

from mreduce import cohn, mk, reduce_matrix

SLACKS = [(1, 30), (2, 40), (2, 80), (3, 80), (4, 40)]


def main():
    budget = int(sys.argv[1])
    for arg in sys.argv[2:]:
        n, cs = arg.split(":")
        n, f = int(n), tuple(int(c) for c in cs.split(","))
        for slack in SLACKS:
            t0 = time.time()
            r = reduce_matrix(cohn(mk((n,)), mk(f)), budget, slack)
            print(n, f, slack, r, round(time.time() - t0, 1), flush=True)


if __name__ == "__main__":
    main()
