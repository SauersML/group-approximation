"""Census of Cohn-type matrices over Z[t, t^-1] with the full-matrix reducer.

Usage: python3 mcensus.py B W budget [mode]
  mode cohn : [[1+pq, p^2], [-q^2, 1-pq]] for p, q with coefficients in [-B, B],
              width <= W, both non-units (no end coefficient +-1 for p) -- all
              pairs, up to the symmetry p <-> q.
  mode prod : products cohn(p1,q1) * cohn(p2,q2) with width <= W.
Prints FAIL lines and a summary.
"""
import itertools
import sys
import time

from mreduce import cohn, mat_mul, mk, reduce_matrix


def polys(B, W):
    rng = range(-B, B + 1)
    for w in range(W + 1):
        for coeffs in itertools.product(rng, repeat=w + 1):
            if coeffs[0] == 0 or coeffs[-1] == 0:
                continue
            if w == 0 and abs(coeffs[0]) == 1:
                continue
            if coeffs[0] < 0:  # sign: cohn(-p,-q) = cohn(p,q), cohn(-p,q) = cohn(p,-q)^T-ish
                continue
            yield coeffs


def main():
    B, W, budget = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    mode = sys.argv[4] if len(sys.argv) > 4 else "cohn"
    ps = list(polys(B, W))
    total = ok = 0
    fails = []
    t0 = time.time()
    maxsteps = 0
    if mode == "cohn":
        items = ((p, q) for p in ps for q in ps + [tuple(-v for v in x) for x in ps] if p <= q or True)
        for p, q in items:
            M = cohn(mk(p), mk(q))
            total += 1
            res, steps, best = reduce_matrix(M, budget)
            if res:
                ok += 1
                maxsteps = max(maxsteps, steps)
            else:
                fails.append((p, q))
                print("FAIL", p, q, best, flush=True)
    else:
        small = [p for p in ps if len(p) <= 2]
        for p1, q1, p2, q2 in itertools.product(small, repeat=4):
            M = mat_mul(cohn(mk(p1), mk(q1)), cohn(mk(p2), mk((0,) + q2)))
            total += 1
            res, steps, best = reduce_matrix(M, budget)
            if res:
                ok += 1
                maxsteps = max(maxsteps, steps)
            else:
                fails.append((p1, q1, p2, q2))
                print("FAIL", p1, q1, p2, q2, best, flush=True)
    print("mode", mode, "B", B, "W", W, "budget", budget, "total", total, "reduced", ok,
          "failed", len(fails), "max steps on success", maxsteps,
          "seconds", round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
