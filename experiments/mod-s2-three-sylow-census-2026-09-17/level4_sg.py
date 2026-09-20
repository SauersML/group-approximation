#!/usr/bin/env python3
"""Test (SG) of mod-s2-short-generated-torelli-relations-pin-one-thirtieth
at the principal congruence level Gamma(4), in the Pbar model of pbar.py.

-I is not in Gamma(4), so pi^-1 Gamma(4) embeds in Mod(S_{0,6}) (as in the
route of mod-s2-three-sylow-torelli-census, Step 1.1).  Its image is the
stabilizer in Pbar of the coset +-Gamma(4) of Gamma(2)/Gamma(4), so Pbar has
[Gamma(2):Gamma(4)]/2 = 512 cosets.  Cosets are keyed by min(key(X), key(-X))
for X mod 4.  Then the same exact pipeline as pbar.py (Reidemeister-Schreier,
unimodular elimination, HNF) gives W, and exact_d.certify checks (SG) on an
LLL basis, with the independent box certificate.

Cross-check: mod-s2-gamma4-torelli-census-is-one-thirtieth reports, in the
B_5 model, h1_rank 54, no torsion, 160 classes, W rank 106, gcd aug 10.

Usage: python3 level4_sg.py [--fast]
"""
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pbar  # noqa: E402
import exact_d  # noqa: E402

S = pbar.S
P = pbar.P
N = 4
POW = np.array([N ** i for i in range(16)], dtype=np.int64)


def canon(X):
    a = int((X.reshape(16) % N) @ POW)
    b = int(((-X).reshape(16) % N) @ POW)
    return min(a, b)


def coset_action(mats):
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


def main(fast):
    t0 = time.time()
    rels = P.check_presentation()
    table = P.conj_table()
    tw = P.standard_twists(table)
    twists = [tuple(w) + tuple(w) for _, w in sorted(tw.items())]
    mats = pbar.pure_mats()
    for u, v in rels:
        assert pbar.is_pm_identity(pbar.word_mat(u, mats) @
                                   pbar.sinv(pbar.word_mat(v, mats)))
    assert pbar.is_pm_identity(pbar.word_mat(P.delta2_pure(), mats))
    for w in twists:
        assert (pbar.word_mat(w, mats) == np.eye(4, dtype=np.int64)).all()
    relators = list(rels) + [(P.delta2_pure(), ())]
    act = coset_action(mats)
    assert len(act) == 512, len(act)
    print(f"[gamma4] Pbar cosets {len(act)} [{time.time()-t0:.0f}s]",
          flush=True)
    ngen, R, vs = pbar.rs(act, relators, twists, reduce_twists=fast)
    print(f"[gamma4] Schreier gens {ngen}, relators {len(R)}, twist vectors "
          f"{len(vs)} [{time.time()-t0:.0f}s]", flush=True)
    elim = None
    if fast:
        import fastelim
        elim = fastelim.eliminate
    label = "gamma4" + ("-fast" if fast else "")
    out, (cols, H, keys, cls_of, B) = S.lattice_from_rs(
        ngen, R, vs, label, len(act), elim=elim)
    json.dump({"name": label, "summary": out, "B": B},
              open(os.path.join(HERE, f"w-{label}.json"), "w"))
    res = exact_d.certify(B, label)
    json.dump(res, open(os.path.join(HERE, f"exact-{label}.json"), "w"),
              indent=1)
    print("saved", label, f"[{time.time()-t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main("--fast" in sys.argv[1:])
