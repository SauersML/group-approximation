#!/usr/bin/env python3
"""Theta balance test (mod-s2-torelli-relations-obey-the-theta-balance-law).

For a finite-index Gamma' <= Gamma(2) the classes O(Gamma') of separating
twists fibre over the ten level-two splittings (the ten 3|3 partitions of the
six Weierstrass points; in the Pbar = PMod(S_{0,6}) model these are the ten
standard twists keyed by triples of {1..5}).  The balance law says: for every
w in W(Gamma'),

    sum_{o over m} w_o  =  aug(w)/10        for each of the ten m      (B)

provided Gamma' <= Gamma(4,8) (the even theta constants theta_m are then
modular forms of weight 1/2 with divisor exactly the Humbert components over
m).  This script recomputes W in the Pbar model (non-fast mode, so twist
vectors are indexed by (coset, twist)) and checks (B) on a Z-basis of W.

Levels: "gamma4" (Gamma(4); by (W) of mod-s2-igusa-torelli-census-is-one-
thirtieth W(Gamma(4,8)) = W(Gamma(4)) with the same classes), and the
3-Sylow chain groups of mod-s2-three-sylow-torelli-census, which lie in
Gamma(2) but not in Gamma(4,8): there (B) is predicted by the transfer step
of the proof node, so these runs test the transfer extension.

Usage: python3 balance.py gamma4 | U | max0 | max1 | max2 | phi
"""
import json
import os
import sys
import time
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
SY = os.path.join(HERE, "..", "mod-s2-three-sylow-census-2026-09-17")
sys.path.insert(0, SY)
import pbar  # noqa: E402

S = pbar.S
P = pbar.P


def gamma4_action(mats):
    N = 4
    POW = np.array([N ** i for i in range(16)], dtype=np.int64)

    def canon(X):
        a = int((X.reshape(16) % N) @ POW)
        b = int(((-X).reshape(16) % N) @ POW)
        return min(a, b)
    mN = [A % N for A in mats]
    start = np.eye(4, dtype=np.int64)
    index, reps, act = {canon(start): 0}, [start], []
    q = 0
    while q < len(reps):
        X = reps[q]
        row = []
        for B in mN:
            Y = (X @ B) % N
            k = canon(Y)
            if k not in index:
                index[k] = len(reps)
                reps.append(Y)
            row.append(index[k])
        act.append(row)
        q += 1
    return act


def sylow_action(name, mats):
    # coset action of the 3-Sylow chain group, as in pbar.main
    return pbar.coset_action(S.subgroup(name), mats)


def main(name):
    t0 = time.time()
    rels = P.check_presentation()
    table = P.conj_table()
    tw = P.standard_twists(table)
    keys = sorted(tw.items())
    labels = [k for k, _ in keys]
    twists = [tuple(w) + tuple(w) for _, w in keys]
    mats = pbar.pure_mats()
    relators = list(rels) + [(P.delta2_pure(), ())]
    if name == "gamma4":
        act = gamma4_action(mats)
    else:
        act = sylow_action(name, mats)
    print(f"[{name}] cosets {len(act)} [{time.time()-t0:.0f}s]", flush=True)
    ngen, R, vs = pbar.rs(act, relators, twists, reduce_twists=False)
    nt = len(twists)
    assert len(vs) == len(act) * nt
    out, (cols, H, ckeys, cls_of, B) = S.lattice_from_rs(
        ngen, R, vs, name, len(act))
    fibre = {}
    for i, c in enumerate(cls_of):
        j = i % nt
        if c in fibre:
            assert fibre[c] == j, "class meets two level-two fibres"
        fibre[c] = j
    ncls = len(ckeys)
    fib_sizes = [sum(1 for c in range(ncls) if fibre[c] == j)
                 for j in range(nt)]
    viol = []
    for r in B:
        aug = sum(r)
        sums = [sum(r[c] for c in range(ncls) if fibre[c] == j)
                for j in range(nt)]
        if any(Fraction(s) != Fraction(aug, 10) for s in sums):
            viol.append({"aug": aug, "fibre_sums": sums})
    res = {"level": name, "cosets": len(act), "classes": ncls,
           "fibre_sizes": fib_sizes, "fibre_labels": [list(l) for l in labels],
           "W_rank": len(B), "gcd_aug": out.get("gcd_aug_W"),
           "h1_rank": out.get("h1_rank"), "h1_torsion": out.get("h1_torsion"),
           "d": out.get("d"),
           "balance_violations": len(viol), "examples": viol[:5],
           "balance_law_holds": not viol,
           "seconds": round(time.time() - t0)}
    print(json.dumps(res), flush=True)
    json.dump(res, open(os.path.join(HERE, f"balance-{name}.json"), "w"),
              indent=1)
    # lattice dump for transversal.py: Z-basis of W and the fibre of each class
    json.dump({"level": name, "fibre": [fibre[c] for c in range(ncls)],
               "B": [list(map(int, r)) for r in B]},
              open(os.path.join(HERE, f"lattice-{name}.json"), "w"))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "gamma4")
