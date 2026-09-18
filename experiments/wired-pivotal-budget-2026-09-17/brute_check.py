#!/usr/bin/env python3
"""Brute-force check of the closed forms in tree_wired_budget.py.

Enumerates every bond configuration of the induced ball B_R (R = 2, 3) of the
3-regular tree, computes P_q(E^w) and the conditional open-pivotal count for
the wired event directly, and compares with the closed form and with
q d/dq log P_q(E^w) (Russo's formula).
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tree_wired_budget import u_tails, wired_prob  # noqa: E402

d = 3


def ball(R):
    V, E, frontier = [()], [], [()]
    for _ in range(R):
        nf = []
        for v in frontier:
            for a in range(d):
                if v and v[-1] == a:
                    continue
                w = v + (a,)
                V.append(w)
                E.append((v, w))
                nf.append(w)
        frontier = nf
    return V, E


def occurs(V, E, S, x, conf):
    par = {v: v for v in V}

    def f(v):
        while par[v] != v:
            par[v] = par[par[v]]
            v = par[v]
        return v

    for e, c in zip(E, conf):
        if c:
            par[f(e[0])] = f(e[1])
    ro, rx = f(()), f(x)
    if ro == rx:
        return True
    rs = {f(s) for s in S}
    return ro in rs and rx in rs


CASES = [(2, k, q) for k in (1, 2) for q in (0.3, 0.55, 0.8)]
CASES += [(3, 1, q) for q in (0.3, 0.55, 0.8)] + [(3, 2, 0.3)]

worst = 0.0
for R in (2, 3):
    V, E = ball(R)
    S = [v for v in V if len(v) == R]
    for k in range(1, R + 1):
        x = tuple([0, 1, 0, 1][:k])
        for q in (0.3, 0.55, 0.8):
            if (R, k, q) not in CASES:
                continue
            tot = piv = 0.0
            for conf in itertools.product((0, 1), repeat=len(E)):
                pr = 1.0
                for c in conf:
                    pr *= q if c else 1 - q
                if occurs(V, E, S, x, conf):
                    tot += pr
                    for j, c in enumerate(conf):
                        if c:
                            cf = list(conf)
                            cf[j] = 0
                            if not occurs(V, E, S, x, cf):
                                piv += pr
            w = wired_prob(d, q, k, R, u_tails(d, q, [R], R + 1)[R])
            err = max(abs(tot - w.v), abs(piv / tot - q * w.d / w.v))
            worst = max(worst, err)
            print(f"R={R} k={k} q={q}: P brute {tot:.10f} formula {w.v:.10f};"
                  f" count brute {piv / tot:.8f} formula {q * w.d / w.v:.8f}")
print("max abs discrepancy", worst)
