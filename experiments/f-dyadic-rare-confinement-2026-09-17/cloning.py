#!/usr/bin/env python3
"""Population-dynamics (cloning) estimates of rare-confinement exponents for Thompson's F on the dyadics.

Node: f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent (and Attempts of
f-dyadic-inverted-orbit-is-subballistic-on-rare-events).

Two quantities, both for mu = uniform on {x0, x0^-1, x1, x1^-1}, x_0 = 1/2.

(1) Lambda_n = -(1/n) log E 2^{-|O_n|}.  The inverted orbit is
    O_n = Phi_{h_1} o ... o Phi_{h_n}({x_0}),  Phi_h(S) = {x_0} u h^{-1} S,
    so (i.i.d. increments, reversed order, symmetric mu) |O_n| has the law of |S_n| for the Markov chain
    S_0 = {x_0}, S_k = {x_0} u h_k S_{k-1}.  E 2^{-|S_n|} = 2^{-1} E prod_k 2^{-[x_0 not in h_k S_{k-1}]}
    is a multiplicative functional, estimated by the Giardina-Kurchan-Peliti cloning algorithm.

(2) Band exponent lambda_C = lim P(O_n subset D_C)^{1/n}, D_C = {k/2^C}.  With w_i = h_1^-1...h_i^-1,
    O_n subset D_C  <=>  x_0 in T_i := w_i^{-1} D_C = h_i T_{i-1} for all i <= n, T_0 = D_C.
    So it is the survival probability of the m-point configuration chain T_i killed when x_0 leaves T_i
    (0/1 weights, same cloning scheme).

Calibrators for (1): F_2 acting on itself (non-EA; -log rho = -log(sqrt3/2) = 0.1438), Z^3 on itself and
the lamplighter Z/2 wr Z on itself (amenable, hence EA, rate -> 0).

Dyadics are exact Python integers a/2^L with L = 1024; any halving of an odd numerator is counted
as 'inexact' and reported (it never occurred in the recorded runs).

Usage: python3 cloning.py [--N 1000] [--n 600] [--seed 1] [--quick]
Runtime: --quick about 1 minute, default a few minutes on one core.
"""
import argparse
import json
import math
import random
import sys
import time

L = 1024
U = 1 << L
INEXACT = [0]


def half(a):
    if a & 1:
        INEXACT[0] += 1
    return a >> 1


def x0(a):
    if a <= U // 2:
        return half(a)
    if a <= 3 * U // 4:
        return a - U // 4
    return 2 * a - U


def x0i(a):
    if a <= U // 4:
        return 2 * a
    if a <= U // 2:
        return a + U // 4
    return half(a + U)


def x1(a):
    if a <= U // 2:
        return a
    if a <= 3 * U // 4:
        return half(a) + U // 4
    if a <= 7 * U // 8:
        return a - U // 8
    return 2 * a - U


def x1i(a):
    if a <= U // 2:
        return a
    if a <= 5 * U // 8:
        return 2 * a - U // 2
    if a <= 3 * U // 4:
        return a + U // 8
    return half(a + U)


GENS = [x0, x0i, x1, x1i]
X0 = U // 2


def check_relations(rng):
    """Check the two defining relators of F on random dyadic points, and that x0, x1 do not commute."""
    def comp(*fs):  # comp(f, g)(t) = f(g(t))
        def h(a):
            for f in reversed(fs):
                a = f(a)
            return a
        return h
    # A = x0, B = x1 as maps; standard relators [A B^-1, A^-1 B A] and [A B^-1, A^-2 B A^2]
    AB = comp(x0, x1i)
    BA = comp(x1, x0i)  # (A B^-1)^-1 = B A^-1
    C1 = comp(x0i, x1, x0)
    C1i = comp(x0i, x1i, x0)
    C2 = comp(x0i, x0i, x1, x0, x0)
    C2i = comp(x0i, x0i, x1i, x0, x0)
    r1 = comp(AB, C1, BA, C1i)
    r2 = comp(AB, C2, BA, C2i)
    ok = True
    noncomm = False
    for _ in range(2000):
        a = rng.randrange(1, U) >> 600 << 600
        ok &= r1(a) == a and r2(a) == a
        noncomm |= x0(x1(a)) != x1(x0(a))
    return ok and noncomm


def resample(rng, pop, weights, N):
    tot = sum(weights)
    if tot == 0:
        return None, 0.0
    return rng.choices(pop, weights=weights, k=N), tot / len(pop)


def cloning_rate(rng, N, n, start, step, report_every):
    """Generic GKP cloning: step(rng, state) -> (new_state, weight). Returns list of (t, -(1/t) log Z_t)."""
    pop = [start] * N
    logZ = 0.0
    out = []
    for t in range(1, n + 1):
        new = []
        ws = []
        for s in pop:
            s2, w = step(rng, s)
            new.append(s2)
            ws.append(w)
        pop, mean_w = resample(rng, new, ws, N)
        if pop is None:
            out.append((t, float("inf")))
            break
        logZ += math.log(mean_w)
        if t % report_every == 0:
            sizes = sorted(len(s) if not isinstance(s, tuple) or len(s) != 2 else 0 for s in pop)
            out.append((t, -logZ / t, sizes[len(sizes) // 2]))
    return out


def f_orbit_step(rng, S):
    g = rng.choice(GENS)
    S2 = frozenset(g(a) for a in S)
    if X0 in S2:
        return S2, 1.0
    return S2 | {X0}, 0.5


def f_band_step(rng, T):
    g = rng.choice(GENS)
    T2 = frozenset(g(a) for a in T)
    return T2, (1.0 if X0 in T2 else 0.0)


def freegroup_step(rng, S):
    # reduced words over letters 1,-1,2,-2; left multiplication by a random generator
    s = rng.choice((1, -1, 2, -2))
    out = set()
    for w in S:
        if w and w[0] == -s:
            out.add(w[1:])
        else:
            out.add((s,) + w)
    S2 = frozenset(out)
    if () in S2:
        return S2, 1.0
    return S2 | {()}, 0.5


def z3_step(rng, S):
    d = rng.choice(((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)))
    S2 = frozenset((p[0] + d[0], p[1] + d[1], p[2] + d[2]) for p in S)
    if (0, 0, 0) in S2:
        return S2, 1.0
    return S2 | {(0, 0, 0)}, 0.5


def lamplighter_step(rng, S):
    # element (lamps frozenset, pos); left multiplication by t^{+-1} shifts everything, by a toggles lamp 0
    s = rng.choice(("t", "T", "a", "a"))
    out = set()
    for f, p in S:
        if s == "t":
            out.add((frozenset(x + 1 for x in f), p + 1))
        elif s == "T":
            out.add((frozenset(x - 1 for x in f), p - 1))
        else:
            out.add((f ^ {0}, p))
    S2 = frozenset(out)
    e = (frozenset(), 0)
    if e in S2:
        return S2, 1.0
    return S2 | {e}, 0.5


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=1000)
    ap.add_argument("--n", type=int, default=600)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    if args.quick:
        args.N, args.n = 300, 200
    rng = random.Random(args.seed)
    res = {"N": args.N, "n": args.n, "seed": args.seed}
    res["relations_ok"] = check_relations(rng)
    print("F relators hold and x0,x1 do not commute:", res["relations_ok"], flush=True)
    rep = max(1, args.n // 10)

    def run(name, start, step, n=args.n, N=args.N):
        t0 = time.time()
        r = cloning_rate(rng, N, n, start, step, rep)
        res[name] = r
        print(name, "%.1fs" % (time.time() - t0), r[-3:], flush=True)

    run("F_dyadic_Lambda", frozenset([X0]), f_orbit_step)
    run("F2_self_Lambda", frozenset([()]), freegroup_step)
    run("Z3_self_Lambda", frozenset([(0, 0, 0)]), z3_step)
    run("lamplighter_self_Lambda", frozenset([(frozenset(), 0)]), lamplighter_step)
    for C in (1, 2, 3, 4, 5, 6):
        T0 = frozenset(k * (U >> C) for k in range(1, 1 << C))
        run("F_band_C%d" % C, T0, f_band_step)
    res["inexact_halvings"] = INEXACT[0]
    print("inexact halvings:", INEXACT[0])
    if args.out:
        with open(args.out, "w") as fh:
            json.dump(res, fh, indent=1)


if __name__ == "__main__":
    sys.exit(main())
