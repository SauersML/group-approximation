#!/usr/bin/env python3
"""Finite checks for the lamplighter calibration of the l2 Morse inequality.

Gamma = Z/2 wr Z, S = {a, t}.  Elements are (lamps, pos) with
(L1, p1)(L2, p2) = (L1 ^ (L2 + p1), p1 + p2).
A = <a_0..a_K> (lamps at 0..K), B = B_2 = <a_1..a_K> (lamps at 1..K).

Checks, for K = 1..5 and random base points gamma:
 1. the graph Y is well defined: gamma b t A = gamma t A for b in B;
 2. phi_1 (t-edges modulo right B-cosets, a-edges killed) kills the chain of
    every relator a^2 and [a, t^k a t^-k] with 1 <= k <= K;
 3. phi_1 kills the path t^k a t^-k (k <= K) used for the correction omega,
    and that path ends at gamma a_k;
 4. the relator [a, t^(K+1) a t^-(K+1)] is NOT killed, so the bound really
    depends on K.
Exit code 0 iff all checks pass.  This is a sanity check of the finite
combinatorics only; the dimension count is in the artifact.
"""
import random
from collections import Counter


def mul(g, h):
    (L1, p1), (L2, p2) = g, h
    return (frozenset(L1 ^ frozenset(x + p1 for x in L2)), p1 + p2)


a = (frozenset([0]), 0)
t = (frozenset(), 1)
ti = (frozenset(), -1)


def coset(g, lo, hi):
    """Canonical representative of g<a_lo..a_hi>: forget lamps at pos+lo..pos+hi."""
    L, p = g
    return (frozenset(x for x in L if not (p + lo <= x <= p + hi)), p)


def phi1(word, g0, K):
    """Signed t-edge chain of the path reading `word` from g0, modulo right B-cosets.

    Letters: 'a' (= a^-1), 't', 'T' = t^-1.
    """
    c = Counter()
    g = g0
    for ch in word:
        if ch == "t":
            c[coset(g, 1, K)] += 1
            g = mul(g, t)
        elif ch == "T":
            g = mul(g, ti)
            c[coset(g, 1, K)] -= 1
        else:
            g = mul(g, a)
    return {k: v for k, v in c.items() if v}, g


def comm(k):
    return "a" + "t" * k + "a" + "T" * k + "a" + "t" * k + "a" + "T" * k


def rand_elem(rng):
    L = frozenset(x for x in range(-6, 7) if rng.random() < 0.5)
    return (L, rng.randint(-5, 5))


def main():
    rng = random.Random(20260917)
    ok = True
    for K in range(1, 6):
        for _ in range(200):
            g = rand_elem(rng)
            for i in range(1, K + 1):
                b = (frozenset([i]), 0)
                if coset(mul(mul(g, b), t), 0, K) != coset(mul(g, t), 0, K):
                    ok = False
                    print("Y ill-defined", K, i)
            for w in ["aa"] + [comm(k) for k in range(1, K + 1)]:
                ch, end = phi1(w, g, K)
                if end != g:
                    ok = False
                    print("relator not closed", K, w)
                if ch:
                    ok = False
                    print("relator not killed", K, w, ch)
            for k in range(1, K + 1):
                ch, end = phi1("t" * k + "a" + "T" * k, g, K)
                if ch or end != mul(g, (frozenset([k]), 0)):
                    ok = False
                    print("correction path fails", K, k)
            ch, end = phi1(comm(K + 1), g, K)
            if end != g or not ch:
                ok = False
                print("longer relator unexpectedly killed", K)
    print("all checks passed" if ok else "FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
