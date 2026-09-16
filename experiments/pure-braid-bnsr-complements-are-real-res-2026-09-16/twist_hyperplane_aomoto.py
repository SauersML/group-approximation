#!/usr/bin/env python3
"""Aomoto cohomology of P_n on and off the twist hyperplanes c_A = 0, with twist depth d(chi).

Context: Cairn claim pure-braid-bnsr-complements-are-real-resonance-varieties (2026-09-16 swarm note).
For chi = sum a_ij omega_ij write c_A = sum_{i<j in A} a_ij (value of chi on the Dehn twist about a curve in
D_n surrounding the strands A, 2 <= |A| <= n-1).  Theorem M of
research/artifacts/pure-braid-twist-nonvanishing-sigma-2026-09-16.md: if no c_A vanishes then chi is in
Sigma^{n-3}(P_n); Theorem M_d: chi is in Sigma^{n-3-d(chi)}(P_n), d(chi) = largest laminar family of zero types.

This script records, for sample integer characters, dim H^i(A(P_n), a /\\) for i <= n-3 (resonance upper bound:
a nonzero H^i with i <= q forces chi outside Sigma^q) and d(chi).  Scope: vanishing over F_p is exact over Q;
nonvanishing is reported for two primes (evidence over Q, not proof).  Nothing here proves Sigma membership.

Usage: timeout 600 python3 twist_hyperplane_aomoto.py   (writes results.json next to this file)
"""
import itertools, json, os, random, sys, time
sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "zp-bf-n-r-first-leaf-star-resonance-2026-09-16"))
from os_resonance_bf import aomoto, PRIMES  # noqa: E402

PAIRS = lambda n: [(i, j) for i in range(1, n + 1) for j in range(i + 1, n + 1)]


def twist(a, A):
    return sum(a.get((i, j), 0) for i, j in itertools.combinations(sorted(A), 2))


def zero_types(a, n):
    return [frozenset(A) for s in range(2, n) for A in itertools.combinations(range(1, n + 1), s)
            if twist(a, A) == 0]


def compatible(A, B):
    return A <= B or B <= A or not (A & B)


def max_laminar(types):
    """largest pairwise compatible (nested or disjoint) subfamily; simple branch and bound."""
    adj = {t: {u for u in types if u != t and compatible(t, u)} for t in types}
    best = [0]

    def grow(size, cand):
        if not cand:
            best[0] = max(best[0], size)
            return
        if size + len(cand) <= best[0]:
            return
        for t in list(cand):
            grow(size + 1, cand & adj[t])
            cand = cand - {t}
            if size + len(cand) <= best[0]:
                return
    grow(0, set(types))
    return best[0]


def sample(n, rng, constraints, scale=10000, tries=2000):
    """random integer character with sum a = 0 and the given twist constraints c_A = 0, otherwise generic."""
    P = PAIRS(n)
    for _ in range(tries):
        a = {p: rng.randint(-scale, scale) for p in P}
        eqs = [tuple(sorted(A)) for A in constraints] + [tuple(range(1, n + 1))]
        # triangular solve: the pivot pair of each constraint lies in its set and in no earlier constraint set
        for k, A in enumerate(eqs):
            free = [p for p in itertools.combinations(A, 2) if not any(set(p) <= set(B) for B in eqs[:k])]
            if not free:
                raise RuntimeError("constraints not triangularizable")
            p = rng.choice(free)
            a[p] -= twist(a, A)
        if any(twist(a, A) for A in eqs):
            continue
        return a
    raise RuntimeError("no sample")


def record(n, a, label, maxdeg):
    dims = [aomoto(n, a, maxdeg, P) for P in PRIMES]
    zt = zero_types(a, n)
    d = max_laminar(zt)
    return {"n": n, "label": label, "a": {f"{i}{j}": v for (i, j), v in sorted(a.items())},
            "H_upto_n_minus_3": dims, "zero_types": sorted(["".join(map(str, sorted(t))) for t in zt]),
            "d": d, "Md_level": max(n - 3 - d, 0)}


CASES = {
    5: [("generic", []), ("c12=0", [(1, 2)]), ("c123=0", [(1, 2, 3)]), ("c1234=0", [(1, 2, 3, 4)]),
        ("c12=c34=0", [(1, 2), (3, 4)]), ("c12=c123=0", [(1, 2), (1, 2, 3)]),
        ("c12=c345=0", [(1, 2), (3, 4, 5)]), ("c123=c345=0", [(1, 2, 3), (3, 4, 5)])],
    6: [("generic", []), ("c12=0", [(1, 2)]), ("c123=0", [(1, 2, 3)]), ("c1234=0", [(1, 2, 3, 4)]),
        ("c12=c34=0", [(1, 2), (3, 4)]), ("c12=c123=0", [(1, 2), (1, 2, 3)]),
        ("c123=c456=0", [(1, 2, 3), (4, 5, 6)]), ("c12=c34=c56=0", [(1, 2), (3, 4), (5, 6)])],
    7: [("c12=0", [(1, 2)])],
}


def block_character(n, blocks, rng, scale=10000):
    """positive control: supported on pairs inside disjoint blocks, zero sum on each block
    (pure-braid-product-projections-obstruct-bnsr-invariants: outside Sigma^D, D = sum(|A_i| - 2))."""
    a = {p: 0 for p in PAIRS(n)}
    for B in blocks:
        ps = list(itertools.combinations(B, 2))
        for p in ps:
            a[p] = rng.randint(-scale, scale)
        a[ps[-1]] -= sum(a[p] for p in ps)
    return a


def rows_zero_character(n, rng, scale=50):
    """positive control for n = 5: all row sums zero (L_U, U = [5]; sunflower claim: outside Sigma^2)."""
    a = {p: 0 for p in PAIRS(n)}
    for _ in range(12):
        i, j, k, l = rng.sample(range(1, n + 1), 4)
        v = rng.randint(1, scale)
        for (x, y), sgn in (((i, j), 1), ((j, k), -1), ((k, l), 1), ((l, i), -1)):
            a[tuple(sorted((x, y)))] += sgn * v
    assert all(sum(a[tuple(sorted((i, j)))] for j in range(1, n + 1) if j != i) == 0 for i in range(1, n + 1))
    return a


CONTROLS = [(5, "control block123 (D=1)", lambda r: block_character(5, [(1, 2, 3)], r)),
            (5, "control rows-zero L_[5] (D=2)", lambda r: rows_zero_character(5, r)),
            (6, "control blocks123,456 (D=2)", lambda r: block_character(6, [(1, 2, 3), (4, 5, 6)], r))]


def main():
    rng = random.Random(20260916)
    out, t0 = [], time.time()

    def emit(rec):
        out.append(rec)
        print(rec["n"], rec["label"], rec["rep"], rec["H_upto_n_minus_3"], "d =", rec["d"],
              "M_d level", rec["Md_level"], f"{time.time() - t0:.1f}s", flush=True)

    for n, label, gen in CONTROLS:
        a = gen(rng)
        rec = record(n, a, label, n - 3)
        rec["rep"] = 0
        emit(rec)
    for n, cases in CASES.items():
        for label, cons in cases:
            for rep in range(3 if n <= 6 else 1):
                rec = record(n, sample(n, rng, cons), label, n - 3)
                rec["rep"] = rep
                emit(rec)
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump({"seed": 20260916, "primes": list(PRIMES), "records": out}, f, indent=1)


if __name__ == "__main__":
    main()
