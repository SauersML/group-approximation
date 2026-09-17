"""Census of level-n Cohn matrices Cohn(n, f) = [[1+nf, n^2], [-f^2, 1-nf]].

Their first rows (1 + n f, n^2) are exactly the unimodular rows (a, n^2) with
a = 1 mod n.  The E_2-class depends only on f mod n (subtract multiples of n^2)
and is trivial when f = +-t^k mod n.  We enumerate f in Z[t] with coefficients
in [0, n-1], constant term nonzero, width <= W, and run the full-matrix reducer.

Usage: python3 level_census.py n W budget
"""
import itertools
import sys
import time

from mreduce import cohn, mk, reduce_matrix


def main():
    n, W, budget = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    t0 = time.time()
    total = ok = 0
    maxsteps = 0
    for w in range(1, W + 1):
        for coeffs in itertools.product(range(n), repeat=w + 1):
            if coeffs[0] == 0 or coeffs[-1] == 0:
                continue
            f = mk(coeffs)
            total += 1
            res, steps, best = reduce_matrix(cohn(mk((n,)), f), budget)
            if res:
                ok += 1
                maxsteps = max(maxsteps, steps)
                print("OK", coeffs, steps, flush=True)
            else:
                print("FAIL", coeffs, best, flush=True)
    print("n", n, "W", W, "budget", budget, "total", total, "reduced", ok,
          "max steps on success", maxsteps, "seconds", round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
