#!/usr/bin/env python3
"""How much cheaper is a window certificate in a Schreier graph of F over an amenable
subgroup?

Mechanism.  Let H <= F and Sch = Sch(F/H, S), S = {x0^{+-1}, x1^{+-1}}.  Cay(F, S) covers
Sch, so ||P_Sch|| >= ||P_F||; and when H is amenable the quasi-regular representation on
l^2(F/H) is weakly contained in the regular one (Kesten), so ||P_Sch|| = ||P_F||.  Hence
lambda_max of any finite window of Sch, over 4, is a lower bound for ||P_F||, exactly as a
window of the Cayley graph is -- but the Schreier ball of radius r has

    |B_r(F) H / H|  <  |B_r(F)|

vertices, and every factor by which its growth rate falls below 2.76 (the measured growth
of |B_r(F)|) is a radius step bought at the same cost.

This script measures that for H = <x0, h> where h is the one-bump element supported on
[1/2, 3/4].  Its x0-conjugates h_n have pairwise disjoint supports (the intervals
[2^{-n-1}, 2^{-n}] and [1-2^{-k}, 1-2^{-k-1}]), so they generate a free abelian group of
infinite rank that x0 shifts: H = Z wr Z, metabelian, amenable.

What is computed, exactly:
  * |H cap B_r(F)| from below, by closing the set of H-elements under right multiplication
    by x0^{+-1} and h_n^{+-1} inside B_R (an H-element of F-length <= R is missed only if
    every H-word reaching it leaves B_R);
  * the number of H-orbits (that is, of cosets Hg) that meet B_r, from above, by union-find
    over the same moves acting on the left -- orbits that the ball disconnects are counted
    more than once, so this is an upper bound on |B_r(F) H / H|.
Both bounds err in the direction that makes the route look *worse*, so the gain reported
here is a lower bound on the real gain.

Usage:  python3 schreier_feasibility.py R [--out out.json]
"""
import argparse
import json
import os
import sys
import time

sys.setrecursionlimit(10000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f_elements import (IDENT, X0, TIDENT, TGENS, comp, inv, key, make, pl_to_tree,  # noqa: E402
                        tinv, tmul, unkey)
from ball_boundary import build_ball  # noqa: E402

# one bump on [1/2, 3/4]: the x0 pattern rescaled to that interval
H_BUMP = make([((0, 1), (0, 1)), ((1, 2), (1, 2)), ((5, 8), (9, 16)),
               ((11, 16), (5, 8)), ((3, 4), (3, 4)), ((1, 1), (1, 1))])


def conj(f, u):
    """u^-1 o f o u."""
    return comp(comp(inv(u), f), u)


def h_family(nmax):
    out = {}
    u = IDENT
    for n in range(0, nmax + 1):
        out[n] = conj(H_BUMP, u)
        u = comp(u, X0)
    u = IDENT
    for n in range(1, nmax + 1):
        u = comp(u, inv(X0))
        out[-n] = conj(H_BUMP, u)
    return out


def supports_disjoint(hs):
    """Check that the bumps have pairwise disjoint supports (as PL maps)."""
    sup = {}
    for n, f in hs.items():
        xs, ys = f
        moved = [xs[i] for i in range(len(xs)) if xs[i] != ys[i]]
        if not moved:
            return False, ("identity bump", n)
        # the support is contained in the interval between the neighbouring fixed points
        lo = max([xs[i] for i in range(len(xs)) if xs[i] == ys[i] and xs[i] < min(moved)])
        hi = min([xs[i] for i in range(len(xs)) if xs[i] == ys[i] and xs[i] > max(moved)])
        sup[n] = (lo, hi)
    items = sorted(sup.items(), key=lambda kv: kv[1][0])
    for (n1, (a1, b1)), (n2, (a2, b2)) in zip(items, items[1:]):
        if b1 > a2:
            return False, (n1, n2)
    return True, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("R", type=int)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    log = lambda s: print(s, file=sys.stderr, flush=True)  # noqa: E731
    t0 = time.time()

    hs = h_family(a.R)
    ok, bad = supports_disjoint(hs)
    keys_H = {}
    for n, f in hs.items():
        keys_H[n] = key(pl_to_tree(f))

    keys, idx, level = build_ball(a.R, log)
    log(f"ball built ({time.time()-t0:.0f}s)")

    # H-elements inside the ball: close under right multiplication by the generators
    gens = [key(TGENS[0]), key(TGENS[1])] + [keys_H[n] for n in hs] + \
           [key(tinv(unkey(keys_H[n]))) for n in hs]
    gens = [g for g in gens if g in idx]
    seen = {key(TIDENT)}
    frontier = [key(TIDENT)]
    while frontier:
        nxt = []
        for k in frontier:
            g = unkey(k)
            for s in gens:
                m = key(tmul(g, unkey(s)))
                if m in idx and m not in seen:
                    seen.add(m)
                    nxt.append(m)
        frontier = nxt
    by_r = [0] * (a.R + 1)
    for k in seen:
        by_r[level[idx[k]]] += 1
    cum = []
    t = 0
    for r in range(a.R + 1):
        t += by_r[r]
        cum.append(t)

    # cosets meeting B_r, from above: union-find under left multiplication by the same gens
    n = len(keys)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry

    for i, k in enumerate(keys):
        g = unkey(k)
        for s in gens:
            m = idx.get(key(tmul(unkey(s), g)))
            if m is not None:
                union(i, m)
    comps = [set() for _ in range(a.R + 1)]
    for i in range(n):
        comps[level[i]].add(find(i))
    cosets = []
    acc = set()
    for r in range(a.R + 1):
        acc |= comps[r]
        cosets.append(len(acc))

    ball = [0] * (a.R + 1)
    for l in level:
        ball[l] += 1
    cball = []
    t = 0
    for r in range(a.R + 1):
        t += ball[r]
        cball.append(t)

    out = {
        "R": a.R,
        "subgroup": "H = <x0, h> with h the one-bump element on [1/2,3/4]; H = Z wr Z, amenable",
        "bumps_have_disjoint_supports": ok,
        "first_overlap": bad,
        "h_word_length_in_F": level[idx[keys_H[0]]] if keys_H[0] in idx else None,
        "ball_sizes": cball,
        "H_in_ball_lower_bound": cum,
        "cosets_meeting_ball_upper_bound": cosets,
        "ball_growth_last": cball[-1] / cball[-2],
        "H_growth_last": (cum[-1] / cum[-2]) if cum[-2] else None,
        "coset_growth_last": cosets[-1] / cosets[-2],
        "seconds": round(time.time() - t0, 1),
        "reading": (
            "CORRECTED 2026-09-18 (referee lens 3). The Schreier-ball growth rate is NOT "
            "measured here, in either direction. cosets_meeting_ball_upper_bound is an "
            "upper bound on the number of cosets meeting B_r, so it upper-bounds |Sch_r|, "
            "but a ratio of upper bounds bounds no ratio: coset_growth_last is not a bound "
            "on the growth rate. Its value 3.02 is in any case above the Cayley growth "
            "2.76, so the pass criterion stated in the earlier version of this field is not "
            "met. From below, |Hg cap B_r| <= |H cap B_{2r}| gives "
            "|Sch_r| >= |B_r| / |H cap B_{2r}|, i.e. at best about 2.76/1.48^2 = 1.26 per "
            "radius at the measured rates. Honest bracket for radius 27: 10^3 to 10^12 "
            "vertices. The mechanism is still sound (Cay covers Sch so ||P_Sch|| >= ||P||, "
            "and H = Z wr Z is amenable so Kesten gives ||P_Sch|| = ||P||); only the saving "
            "is unpriced. Blockers: a canonical form for the cosets Hg, and the "
            "Schreier-ball growth rate itself."),
    }
    text = json.dumps(out, indent=1)
    if a.out:
        open(a.out, "w").write(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
