#!/usr/bin/env python3
"""Sanity check of the commutator transfer lemma (2026-09-16).

Lemma. Let A, B in Sym(n) and A', B' in Sym(t), t >= n, with [n] a subset of [t].
Put E_s = {x in [n] : S x != S' x} for S in {A, B}. Then

    |{x in [n] : [A,B] x != [A',B'] x}| <= 2 (|E_A| + |E_B|),

where [A,B] = A B A^-1 B^-1 acts by x -> A(B(A^-1(B^-1 x))).

The proof in research/artifacts/thompson-f-stability-variants-2026-09-16.md is
complete; this script only guards against slips in the constant. It checks the
inequality exhaustively for (n,t) in {(2,2),(2,3),(2,4),(3,3),(3,4),(3,5),(4,4)}
over ALL A,B in Sym(n) and ALL A',B' in Sym(t) (no commuting hypothesis), and on
random near-extensions for larger n. It reports the largest observed ratio
|moved difference| / (|E_A|+|E_B|) and whether 2 is attained.

Pure python3, single thread, a few seconds to a minute.
"""
import itertools
import random
import sys


def inv(p):
    q = [0] * len(p)
    for i, j in enumerate(p):
        q[j] = i
    return q


def comm_at(A, B, Ai, Bi, x):
    return A[B[Ai[Bi[x]]]]


def diff_count(A, B, Ap, Bp, n):
    Ai, Bi, Api, Bpi = inv(A), inv(B), inv(Ap), inv(Bp)
    return sum(1 for x in range(n) if comm_at(A, B, Ai, Bi, x) != comm_at(Ap, Bp, Api, Bpi, x))


def err(S, Sp, n):
    return sum(1 for x in range(n) if S[x] != Sp[x])


def exhaustive(n, t):
    perms_n = [list(p) for p in itertools.permutations(range(n))]
    perms_t = [list(p) for p in itertools.permutations(range(t))]
    worst = 0.0
    attained = False
    checks = 0
    for A in perms_n:
        Ai = inv(A)
        for B in perms_n:
            Bi = inv(B)
            cAB = [comm_at(A, B, Ai, Bi, x) for x in range(n)]
            for Ap in perms_t:
                ea = err(A, Ap, n)
                Api = inv(Ap)
                for Bp in perms_t:
                    eb = err(B, Bp, n)
                    Bpi = inv(Bp)
                    d = sum(1 for x in range(n) if cAB[x] != comm_at(Ap, Bp, Api, Bpi, x))
                    checks += 1
                    if d > 2 * (ea + eb):
                        print("COUNTEREXAMPLE", n, t, A, B, Ap, Bp, d, ea, eb)
                        sys.exit(1)
                    if ea + eb > 0:
                        r = d / (ea + eb)
                        if r > worst:
                            worst = r
                        if d == 2 * (ea + eb):
                            attained = True
    return checks, worst, attained


def random_trials(trials, seed=20260916):
    rng = random.Random(seed)
    worst = 0.0
    for _ in range(trials):
        n = rng.randint(2, 60)
        t = n + rng.randint(0, 20)
        A = list(range(n)); rng.shuffle(A)
        B = list(range(n)); rng.shuffle(B)
        # extend to [t] and perturb by a few random transpositions
        Ap = A + list(range(n, t))
        Bp = B + list(range(n, t))
        for S in (Ap, Bp):
            for _k in range(rng.randint(0, 4)):
                i, j = rng.randrange(t), rng.randrange(t)
                S[i], S[j] = S[j], S[i]
        ea, eb = err(A, Ap, n), err(B, Bp, n)
        d = diff_count(A, B, Ap, Bp, n)
        if d > 2 * (ea + eb):
            print("COUNTEREXAMPLE (random)", n, t, A, B, Ap, Bp, d, ea, eb)
            sys.exit(1)
        if ea + eb > 0:
            worst = max(worst, d / (ea + eb))
    return worst


if __name__ == "__main__":
    for (n, t) in [(2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (4, 4)]:
        checks, worst, attained = exhaustive(n, t)
        print(f"exhaustive n={n} t={t}: {checks} quadruples, max ratio {worst:.4f}, ratio 2 attained: {attained}")
    w = random_trials(20000)
    print(f"random near-extensions (20000 trials, n<=60, t<=80): max ratio {w:.4f}")
    print("no counterexample")
