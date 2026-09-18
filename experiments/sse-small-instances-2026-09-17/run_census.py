#!/usr/bin/env python3
"""Replay driver for the certified numbers of the small F_2^k Cayley SSE census.

Asserts (exit status 0 only if every assertion holds):

 (A) noisy cube Cay(F_2^k, rho): exact max stay at |S| = s equals the best subgroup (subcube)
     for rho in {1/8, 1/4, 3/8}, (k, s) in {4}x{2,4,8}, {5}x{2,4,8,16}, {6,7}x{2,4,8};
     and the exact k = 6, 7, s = 8 values against the Delsarte LP (= basic SDP) and EIG.
 (B) Cay(F_2^7, weight <= 2), s = 8: exact optimum 1/4 is attained by the ball {0, e_1..e_7}
     and every 3-dimensional subgroup has stay <= 3/14 < 1/4 (a non-subgroup optimum).
 (C) s = 4 subgroup domination: on random integer weights (k = 5, 6) the exact s = 4 optimum
     equals the best 2-dimensional subgroup (the proof is by hand; this is a regression check).
 (D) basic-SDP gaps for unweighted generator sets found by search_gaps.py.
 (E) subgroup-dominance constants C(S) (theta = 1) of subgroup_dominance.py:
     exhaustive k = 4, s = 8 gives max C = 1; the ball k = 7 gives 22/21; the local-search
     witnesses give 52/51 (k=5,s=8), 22/21 (k=6,s=8), 70/69 (k=6,s=16).
 (F) spectral-sampling theorem checks, in exact rational arithmetic: d_S(a) = 2 Pr_mu[a.y = 1],
     mu(V) <= |V| delta for dim V < c, the exact miss probability of the sampled subgroup is
     at most E_c d_S(a)/2 (k <= 4), and C(S) <= E_c/2 on random sets and the extremal witnesses.
Exact values use the integer branch and bound sse_exact.c (compiled with gcc).
"""
import random, sys
from fractions import Fraction
from sse_cayley import (noisy_cube, exact_c, best_subspace, sdp_cert, eig_cert, stay,
                        popcount, subspaces)
from subgroup_dominance import C_theta, exhaustive

def close(x, y, tol=1e-6):
    return abs(x - y) < tol

def part_A():
    for num, den in [(1, 8), (1, 4), (3, 8)]:
        for k, sizes in [(4, [2, 4, 8]), (5, [2, 4, 8, 16]), (6, [2, 4, 8]), (7, [2, 4, 8])]:
            w = noisy_cube(k, num, den)
            for s in sizes:
                sub = best_subspace(k, w, s)
                ex, S, _ = exact_c(k, w, s, lower=sub)
                assert close(ex, sub, 1e-12), (k, num, den, s, ex, sub)
                print(f"A noisy rho={num}/{den} k={k} s={s}: exact = subcube = {ex:.6f}")
    table = {  # (k, num, den): (exact, sdp, eig) at s = 8
        (6, 1, 4): (0.296703, 0.306800, None),
        (6, 1, 8): (0.401170, 0.411260, None),
        (6, 3, 8): (0.196232, 0.200390, None),
        (7, 1, 4): (0.211101, 0.219741, 0.314785),
        (7, 1, 8): (0.318598, 0.333577, 0.459702),
        (7, 3, 8): (0.119798, 0.123512, 0.172290),
    }
    for (k, num, den), (ex0, sdp0, eig0) in table.items():
        w = noisy_cube(k, num, den)
        ex, _, _ = exact_c(k, w, 8, lower=best_subspace(k, w, 8))
        sdp = sdp_cert(k, w, 8)
        eig = eig_cert(k, w, 8)
        assert close(ex, ex0), (k, num, den, ex)
        assert abs(sdp - sdp0) < 5e-4 and sdp > ex + 3e-3, (k, num, den, sdp)
        if eig0 is not None:
            assert close(eig, eig0), (k, num, den, eig)
        assert eig > sdp
        print(f"A table k={k} rho={num}/{den} s=8: exact {ex:.6f}  SDP {sdp:.6f}  EIG {eig:.6f}")

def part_B():
    k = 7
    w = {a: 1 for a in range(1, 1 << k) if popcount(a) <= 2}
    ball = [0] + [1 << i for i in range(k)]
    assert Fraction(stay(k, w, ball)).limit_denominator(1000) == Fraction(1, 4)
    sub = best_subspace(k, w, 8)
    assert close(sub, 3 / 14), sub
    ex, S, _ = exact_c(k, w, 8, lower=0.25)
    assert close(ex, 0.25), ex
    print(f"B weight<=2 graph k=7 s=8: exact {ex} (witness {S}), best subgroup {sub:.6f} = 3/14,"
          f" SDP {sdp_cert(k, w, 8):.6f}")

def part_C():
    rng = random.Random(20260917)
    for k in (5, 6):
        for trial in range(20):
            w = {a: rng.randint(0, 9) for a in range(1, 1 << k)}
            w = {a: x for a, x in w.items() if x > 0}
            sub = best_subspace(k, w, 4)
            ex, _, _ = exact_c(k, w, 4, lower=sub)
            assert close(ex, sub, 1e-12), (k, trial, ex, sub)
    print("C s=4: exact == best subgroup on 40 random weighted Cayley graphs (k = 5, 6)")

def part_D():
    cases = [(5, [9, 18, 26, 27, 28, 31], 6, 0.5, 0.583333),
             (5, [14, 15, 17, 24, 25, 26, 29], 4, None, None),
             (6, [5, 12, 16, 30, 40, 42, 53, 61], 4, None, None),
             (6, [1, 10, 25, 34, 48, 56, 60], 8, None, None)]
    for k, D, s, ex0, sdp0 in cases:
        w = {a: 1 for a in D}
        sub = best_subspace(k, w, s)
        ex, S, _ = exact_c(k, w, s, lower=sub or 0.0)
        sdp = sdp_cert(k, w, s)
        if ex0 is not None:
            assert close(ex, ex0) and close(sdp, sdp0), (ex, sdp)
        assert sdp > ex + 0.03, (k, D, s, ex, sdp)
        print(f"D k={k} D={D} s={s}: exact {ex:.6f} SDP {sdp:.6f} gap {sdp - ex:.4f} sub {sub}")

def part_E():
    (Cmax, argmax), hist = exhaustive(4, 8, 1.0)
    assert close(Cmax, 1.0) and sum(hist.values()) == 6435, (Cmax, hist)
    print("E exhaustive k=4 s=8: max C = 1 over all 6435 sets containing 0")
    k = 7
    C, _, d = C_theta(k, [0] + [1 << i for i in range(k)], 1.0)
    assert close(C, 22 / 21), C
    print(f"E ball k=7: C = {C:.6f} = 22/21, d_min = {d.min()}")
    for k, S, val in [(5, [0, 3, 4, 9, 16, 20, 24, 29], Fraction(52, 51)),
                      (6, [0, 5, 17, 27, 49, 60, 61, 63], Fraction(22, 21)),
                      (6, [0, 7, 8, 17, 18, 22, 24, 33, 34, 38, 44, 47, 51, 52, 58, 62], Fraction(70, 69))]:
        C, _, _ = C_theta(k, S, 1.0)
        assert close(C, float(val)), (k, S, C)
        print(f"E witness k={k} s={len(S)}: C = {C:.6f} = {val}")

def spectral_measure(k, S):
    """mu(y) = N |1_S^(y)|^2 / s, a probability measure on the dual F_2^k."""
    N = 1 << k
    s = len(S)
    mu = []
    for y in range(N):
        t = sum(-1 if popcount(x & y) & 1 else 1 for x in S)
        mu.append(Fraction(t * t, N * s))
    assert sum(mu) == 1
    return mu

def sampling_miss_probability(k, c, mu, a):
    """Exact Pr[a not in H] for H = V^perp, V = span of iid mu-samples stopped at dim V = c."""
    memo = {}
    def span_add(V, y):
        return frozenset(V | {v ^ y for v in V})
    def f(V, hit):
        if len(V) == 1 << c:
            return Fraction(int(hit))
        key = (V, hit)
        if key not in memo:
            stay_mass = sum(mu[v] for v in V)
            tot = Fraction(0)
            for y in range(1 << k):
                if y not in V and mu[y]:
                    tot += mu[y] * f(span_add(V, y), hit or popcount(a & y) & 1 == 1)
            memo[key] = tot / (1 - stay_mass)
        return memo[key]
    return f(frozenset({0}), False)

def part_F():
    """Spectral-sampling theorem: C(S) <= E_c / 2 with E_c = sum_{i=1}^c 1/(1 - 2^-i)."""
    rng = random.Random(7)
    def E(c):
        return sum(Fraction(1) / (1 - Fraction(1, 2 ** i)) for i in range(1, c + 1))
    for k, s, trials in [(3, 4, 30), (4, 2, 10), (4, 4, 20), (4, 8, 20), (5, 4, 10), (5, 8, 10)]:
        c = k - (s.bit_length() - 1)
        N = 1 << k
        for _ in range(trials):
            S = [0] + rng.sample(range(1, N), s - 1)
            mu = spectral_measure(k, S)
            Sset = set(S)
            for a in range(1, N):
                d = Fraction(sum(1 for v in S if v ^ a not in Sset), s)
                assert d == 2 * sum(mu[y] for y in range(N) if popcount(a & y) & 1), (S, a)
            for j in range(c):
                for V in subspaces(k, j):
                    assert sum(mu[v] for v in V) <= Fraction(len(V), N // s), (S, V)
            if k <= 4:
                for a in range(1, N):
                    d = Fraction(sum(1 for v in S if v ^ a not in Sset), s)
                    miss = sampling_miss_probability(k, c, mu, a)
                    assert miss <= E(c) * d / 2, (S, a, miss, d)
            C, _, _ = C_theta(k, S, 1.0)
            assert C <= float(E(c)) / 2 + 1e-9, (S, C, E(c))
        print(f"F k={k} s={s} c={c}: identity d = 2 Pr_mu, mu(V) <= |V| delta, Wald bound and"
              f" C(S) <= E_c/2 = {float(E(c)) / 2:.4f} on {trials} random sets")
    for k, S in [(7, [0] + [1 << i for i in range(7)]), (6, [0, 5, 17, 27, 49, 60, 61, 63])]:
        c = k - 3
        C, _, _ = C_theta(k, S, 1.0)
        assert C <= float(E(c)) / 2
        print(f"F extremal witness k={k} s=8: C = {C:.6f} <= E_c/2 = {float(E(c)) / 2:.4f}")

if __name__ == "__main__":
    parts = sys.argv[1:] or ["A", "B", "C", "D", "E", "F"]
    for p in parts:
        globals()["part_" + p]()
    print("ALL ASSERTIONS PASSED")
