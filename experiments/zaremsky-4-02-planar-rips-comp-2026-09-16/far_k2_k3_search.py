#!/usr/bin/env python3
"""Adversarial search for five planar points a, a', p1, p2, p3 with
|a - a'| > r, |p_i - p_j| > r and all six cross distances <= r (r = 1).

The artifact proves no such configuration exists (crossing-diagonal argument).
Here we maximise the minimum slack by random restarts and hill climbing; a
positive slack would contradict the lemma.  Evidence only; single-threaded.
Usage: python3 far_k2_k3_search.py SEED RESTARTS
"""
import math
import random
import sys


def slack(P, npts=3):
    """npts = 3: the forbidden pattern; npts = 2: the square pattern, which
    exists (calibration: positive slack expected)."""
    a, b, p = P[0], P[1], P[2:2 + npts]
    s = [math.dist(a, b) - 1.0]
    for i in range(npts):
        for j in range(i + 1, npts):
            s.append(math.dist(p[i], p[j]) - 1.0)
        s.append(1.0 - math.dist(a, p[i]))
        s.append(1.0 - math.dist(b, p[i]))
    return min(s)


def climb(rng, npts, iters=3000):
    n = 2 + npts
    P = [(rng.uniform(-1.5, 1.5), rng.uniform(-1.5, 1.5)) for _ in range(n)]
    cur = slack(P, npts)
    step = 0.3
    for it in range(iters):
        k = rng.randrange(n)
        Q = list(P)
        Q[k] = (P[k][0] + rng.gauss(0, step), P[k][1] + rng.gauss(0, step))
        v = slack(Q, npts)
        if v >= cur:
            P, cur = Q, v
        if it % 500 == 499:
            step *= 0.5
    return cur


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    rng = random.Random(seed)
    calib = max(climb(rng, 2) for _ in range(50))
    print("calibration (square pattern, should be > 0): %.6g" % calib)
    assert calib > 0
    best = max(climb(rng, 3) for _ in range(restarts))
    print("seed", seed, "restarts", restarts, "best min-slack %.6g" % best)
    print("positive slack would be a counterexample:", best > 0)


if __name__ == "__main__":
    main()
