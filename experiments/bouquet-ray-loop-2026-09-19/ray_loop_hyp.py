#!/usr/bin/env python3
"""Hypotheses (Omega), (E), (F) of `fp-self-similar-groups-have-fp-ray-loop-subgroups` at the rays
c^infinity, for the generators {a, e, S, T} of each linear bouquet, and the support data of
the proof (item 1 of `linear-bouquet-recursions-ray-loop-and-contraction`).

W = letterwise section closure of the generators and their inverses (finite: unit weight).
Along a ray v c^infinity every word of W is followed by u -> u|_c inside W; (E) holds at c
iff every cycle of this map is a fixed word, and (Omega) holds iff every fixed word fixes c.
The eventual sections are then the fixed words.  Checked for every c in X (c = z and c != z).
Also printed: the off-ray supports of S and T (points y != z with a nontrivial section),
whether they are disjoint, and whether sigma = tau = 1.
Run: nice -n 10 timeout 1200 python3 ray_loop_hyp.py > ray_loop_hyp.out
"""
from bouquets import bouquets
from loopgraph import N, ID, reduce, inv, fmt, W

def eventual(R, Wset, c):
    fixed, ok_E, ok_O = set(), True, True
    for u in Wset | {()}:
        seen, v = [], u
        while v not in seen: seen.append(v); v = reduce(R.sec(v, c))
        cyc = seen[seen.index(v):]
        if len(cyc) > 1: ok_E = False
        elif v:
            fixed.add(v)
            if R.perm(v)[c] != c: ok_O = False
    return ok_E, ok_O, fixed

if __name__ == "__main__":
    tally = {}
    for name, R, I in bouquets():
        gens = [W("a"), W("e"), I["S"], I["T"]]
        Wset = R.closure(gens + [inv(g) for g in gens])
        z = I["z"]; ok, other = True, []
        okE, okO, Cz = eventual(R, Wset, z)
        want = {I["S"], inv(I["S"]), I["T"], inv(I["T"])}
        ok = okE and okO and Cz == want
        for c in range(N):
            if c == z: continue
            e1, o1, Cc = eventual(R, Wset, c)
            if not (e1 and o1 and not Cc): other.append(c)
        suppS = {y for y in range(N) if y != z and R.sec(I["S"], y)}
        suppT = {y for y in range(N) if y != z and R.sec(I["T"], y)}
        trivroots = I["sigma"] == ID and I["tau"] == ID
        key = (ok, not other, not (suppS & suppT), trivroots)
        tally[key] = tally.get(key, 0) + 1
        print(name, "| z =", z, "| (Omega),(E) at z:", okE and okO, "| C_z = {S,T}^{+-1}:", Cz == want,
              "| other c with loops:", other, "| supp S", sorted(suppS), "supp T", sorted(suppT),
              "| sigma = tau = 1:", trivroots, flush=True)
    print("\n(C_z = {S,T}^{+-1} with (Omega),(E); no loop at c != z; disjoint off-ray supports; sigma = tau = 1) : count")
    for k, v in sorted(tally.items()): print(" ", k, ":", v)
