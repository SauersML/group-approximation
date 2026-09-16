#!/usr/bin/env python3
"""Twist depth d(Phi_k) of the braid restrictions Phi_k of full-twist-invisible characters of bF_{n,r}.

Context: Theorem M_d (research/pure-braid-twist-depth-d-characters-lie-in-sigma-n-3-d.md) puts a character of P_k
in Sigma^{k-3-d} when its twist depth d <= k-4.  If k - 3 - d(Phi_k) -> infinity along k = r mod (n-1), then
Lemma 5 of research/artifacts/zp-pure-braided-bht-sigma-2026-09-13.md would give Sigma^infinity for that phi without
the resonance conjecture.  This script records, for random integer points of W_0 (os_resonance_bf.random_W0) and
for first-leaf characters, the zero types (subsets S of [k], 2 <= |S| <= k-1, with sum_{i<j in S} Phi_k(A_ij) = 0),
how many are intervals, and the largest laminar family d(Phi_k).  Evidence only; nothing here is a proof.

Usage: timeout 600 python3 bf_twist_depth.py   (writes bf_twist_depth.json next to this file)
"""
import itertools, json, os, random, sys, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "zp-bf-n-r-first-leaf-star-resonance-2026-09-16"))
from os_resonance_bf import Phi, random_W0, first_leaf  # noqa: E402
from twist_hyperplane_aomoto import max_laminar  # noqa: E402


def zero_types(a, k):
    out = []
    for size in range(2, k):
        for S in itertools.combinations(range(1, k + 1), size):
            if sum(a[(i, j)] for i, j in itertools.combinations(S, 2)) == 0:
                out.append(frozenset(S))
    return out


def greedy_laminar(types):
    """lower bound for the largest laminar subfamily: add types by increasing size when compatible."""
    fam = []
    for S in sorted(types, key=len):
        if all(S <= T or T <= S or not (S & T) for T in fam):
            fam.append(S)
    return len(fam)


def is_interval(S):
    return max(S) - min(S) + 1 == len(S)


def record(n, r, k, data, label):
    a = Phi(data, n, r, k)
    zt = zero_types(a, k)
    t = time.time()
    exact = len(zt) <= 150
    d = max_laminar(zt) if exact else greedy_laminar(zt)
    return {"n": n, "r": r, "k": k, "label": label, "zero_types": len(zt),
            "interval_zero_types": sum(map(is_interval, zt)),
            "non_interval_examples": sorted(["".join(f"{x}," for x in sorted(S))[:-1] for S in zt
                                             if not is_interval(S)])[:6],
            "d": d, "d_exact": exact, "Md_level": k - 3 - d, "tree_bound_intervals_only": (k - 2) // (n - 1),
            "laminar_seconds": round(time.time() - t, 2)}


def main():
    rng = random.Random(20260916)
    out, t0 = [], time.time()
    plan = [(3, 1, (5, 7, 9, 11, 13)), (3, 2, (6, 8, 10, 12)), (4, 1, (7, 10, 13)), (4, 2, (8, 11))]
    for n, r, ks in plan:
        pts = [random_W0(n, r, rng, scale=1000) for _ in range(2)]
        c = [rng.randint(1, 1000) for _ in range(n - 1)]
        for k in ks:
            for i, data in enumerate(pts):
                rec = record(n, r, k, data, f"random W0 #{i}")
                out.append(rec)
                print(rec["n"], rec["r"], rec["k"], rec["label"], "zero types", rec["zero_types"],
                      "intervals", rec["interval_zero_types"], "d", rec["d"], "level", rec["Md_level"],
                      f"{time.time() - t0:.1f}s", flush=True)
            rec = record(n, r, k, first_leaf(c, n, r), "first leaf")
            out.append(rec)
            print(rec["n"], rec["r"], rec["k"], rec["label"], "zero types", rec["zero_types"],
                  "d", rec["d"], "exact" if rec["d_exact"] else "greedy lower bound", "level", rec["Md_level"],
                  f"{time.time() - t0:.1f}s", flush=True)
    with open(os.path.join(HERE, "bf_twist_depth.json"), "w") as f:
        json.dump({"seed": 20260916, "records": out}, f, indent=1)


if __name__ == "__main__":
    main()
