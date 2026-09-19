#!/usr/bin/env python3
"""Sanity check for Lemma U of
research/artifacts/erasable-pattern-avoiding-cover-pairs-2026-09-19.md.

Lemma U: given finite K ⊆ L ⊆ G and patterns u != u' on L that agree off K, for a large finite
L' ⊇ L a uniformly random context c on L' \\ L makes w' = u' ∪ c "unbordered against w = u ∪ c":
for every h != 1 with hL' ∩ K != ∅ there is k in L' ∩ hL' with w(k) != w'(h^-1 k).

This script checks the statement (not the proof) on the free group F_2 and on Z, with L' a word ball.
It reports, for each radius R, the fraction of random contexts that satisfy the condition and the
union bound of the proof, sum_h |A|^{-(|L' ∩ hL'| - 2|L|)/2}.

Run: python3 check_unbordered_context.py  (deterministic seed; a few seconds)
"""
import itertools
import random

INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def red(w):
    out = []
    for ch in w:
        if out and out[-1] == INV[ch]:
            out.pop()
        else:
            out.append(ch)
    return "".join(out)


def mul(x, y):
    return red(x + y)


def inv(x):
    return "".join(INV[c] for c in reversed(x))


def ball_f2(R):
    level = [""]
    ball = {""}
    for _ in range(R):
        nxt = []
        for w in level:
            for c in "aAbB":
                v = red(w + c)
                if v not in ball:
                    ball.add(v)
                    nxt.append(v)
        level = nxt
    return ball


class F2:
    mul = staticmethod(mul)
    inv = staticmethod(inv)
    one = ""
    ball = staticmethod(ball_f2)


class Zgrp:
    mul = staticmethod(lambda x, y: x + y)
    inv = staticmethod(lambda x: -x)
    one = 0
    ball = staticmethod(lambda R: set(range(-R, R + 1)))


def check(G, K, L, u, up, Lp, alphabet, trials, rng):
    ctx = sorted(Lp - L, key=str)
    # all h != 1 with hL' ∩ K nonempty: h = k l^-1
    H = {G.mul(k, G.inv(l)) for k in K for l in Lp} - {G.one}
    good = 0
    for _ in range(trials):
        c = {p: rng.choice(alphabet) for p in ctx}
        w = dict(c)
        w.update(u)
        wp = dict(c)
        wp.update(up)
        ok = True
        for h in H:
            hi = G.inv(h)
            clash = False
            for k in Lp:
                q = G.mul(hi, k)
                if q in Lp and w[k] != wp[q]:
                    clash = True
                    break
            if not clash:
                ok = False
                break
        good += ok
    # union bound
    ub = 0.0
    for h in H:
        ov = sum(1 for k in Lp if G.mul(G.inv(h), k) in Lp)
        ub += len(alphabet) ** (-(ov - 2 * len(L)) / 2)
    return good / trials, len(H), ub


def main():
    rng = random.Random(20260919)
    A = [0, 1]
    # F_2: K = {1, a}, memory-like L = ball of radius 1 (contains K M^-1 M for M = {1,a})
    for R in (2, 3, 4, 5):
        L = ball_f2(1)
        K = {"", "a"}
        u = {p: rng.choice(A) for p in L}
        up = dict(u)
        up[""] = 1 - u[""]
        Lp = ball_f2(R)
        frac, nh, ub = check(F2, K, L, u, up, Lp, A, 200, rng)
        print(f"F2  R={R} |L'|={len(Lp)} #h={nh} good-fraction={frac:.3f} union-bound={ub:.3g}")
    for R in (4, 8, 16, 32, 64):
        L = set(range(-2, 3))
        K = {0, 1}
        u = {p: rng.choice(A) for p in L}
        up = dict(u)
        up[0] = 1 - u[0]
        up[1] = 1 - u[1]
        Lp = set(range(-R, R + 1))
        frac, nh, ub = check(Zgrp, K, L, u, up, Lp, A, 200, rng)
        print(f"Z   R={R} |L'|={len(Lp)} #h={nh} good-fraction={frac:.3f} union-bound={ub:.3g}")


if __name__ == "__main__":
    main()
