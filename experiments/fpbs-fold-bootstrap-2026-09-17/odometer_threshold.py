#!/usr/bin/env python3
"""Checks for sections 2 and 3 of research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md.

(A) Odometer (Lemma 2.1): on Z/N with triples {q, q+1, q+t} (w, a w, b w),
    the 2-of-3 closure of {0..m}, m = max(|t|,1), is all of Z/N for every t
    (triple members counted with multiplicity: for t = 1 the points a w, b w
    are distinct but share a coordinate).  By cl(pi^-1 S) >= pi^-1 cl(S) this bounds the
    closure on any free action with the chi-odometer factor.
(B) iid threshold (Section 3): y = least fixed point of
    f(y) = p + (1-p)(2y^2 - y^4); closure conull iff y = 1 iff p > 5/32.
    Exact rational checks, plus iteration on both sides of 5/32.
(C) Monte Carlo on the F_2 Cayley hypertree: fraction of the root's closure
    events for iid seeds restricted to a ball (a lower bound for finite radius).
Usage: odometer_threshold.py
"""
import random
from fractions import Fraction as Fr


def zn_closure(N, t, seeds):
    S = set(seeds)
    changed = True
    while changed:
        changed = False
        for q in range(N):
            T = [q % N, (q + 1) % N, (q + t) % N]
            inn = [x in S for x in T]
            if sum(inn) == 2:
                S.add(T[inn.index(False)])
                changed = True
    return S


def part_a():
    for t in (-3, -1, 0, 2, 5, 1):
        m = max(abs(t), 1)
        for N in (m + 2, 17, 64, 101):
            full = len(zn_closure(N, t, range(m + 1))) == N
            print(dict(test="odometer", t=t, N=N, seeds=m + 1, closure_full=full))


def f(p, y):
    return p + (1 - p) * (2 * y * y - y ** 4)


def part_b():
    p = Fr(5, 32)
    y = Fr(1, 3)
    assert f(p, y) == y
    q = 1 - p
    assert q * (4 * y - 4 * y ** 3) == 1  # tangency
    dens = p + q * (1 - (1 - y * y) ** 3)
    print(dict(test="threshold_exact", p="5/32", fixed_point="1/3", tangent=True,
               closure_density=str(dens)))
    for pp in (0.150, 0.155, 5 / 32, 0.1575, 0.16, 0.20):
        yy = 0.0
        for _ in range(200000):
            yy = f(pp, yy)
        print(dict(test="threshold_iter", p=round(pp, 6), y=round(yy, 6)))


def part_c(radius=7, reps=400, rng=None):
    rng = rng or random.Random(5032)
    INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}

    def lmul(x, w):
        return w[1:] if w and w[0] == INV[x] else x + w

    ball = [""]
    layer = [""]
    for _ in range(radius):
        nxt = [x + w for w in layer for x in "aAbB" if not w or w[0] != INV[x]]
        ball += nxt
        layer = nxt
    pos = set(ball)
    for p in (0.12, 5 / 32, 0.19, 0.25):
        hits = 0
        for _ in range(reps):
            S = {w for w in ball if rng.random() < p}
            changed = True
            while changed:
                changed = False
                for w in ball:
                    T = (w, lmul("a", w), lmul("b", w))
                    if not all(x in pos for x in T):
                        continue
                    inn = [x in S for x in T]
                    if sum(inn) == 2:
                        S.add(T[inn.index(False)])
                        changed = True
            hits += "" in S
        print(dict(test="hypertree_mc", radius=radius, p=round(p, 5), reps=reps,
                   root_in_closure=round(hits / reps, 3)))


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
