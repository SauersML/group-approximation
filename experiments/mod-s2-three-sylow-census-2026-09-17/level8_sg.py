#!/usr/bin/env python3
"""Test (SG) of mod-s2-short-generated-torelli-relations-pin-one-thirtieth
on the index-two subgroups Gamma(8) < G_chi < Gamma(4), in the Pbar model.

G_chi = ker(chi) for a nonzero functional chi on Gamma(4)/Gamma(8) = sp_4(F_2)
(the orbit representatives of ../mod-s2-gamma4-index2-census-2026-09-17/
index2.py, one per Sp_4(F_2)-orbit).  -I is not in G_chi, so pi^-1 G_chi
embeds in Mod(S_{0,6}); its image is the stabilizer in Pbar of the coset
+-G_chi, and Pbar has [Gamma(2) : G_chi]/2 = 1024 cosets.  Gamma(2) acts
trivially on Gamma(4)/Gamma(8) by conjugation, so G_chi is normal in Gamma(2)
and cosets are keyed as in index2.enumerate_chi: (A mod 4 up to sign,
chi(X)) with X = A L^-1 normalised to X = I mod 4.

The exact pipeline is that of pbar.py; exact_d.certify checks (SG) on an LLL
basis of W and runs the independent box certificate.

Usage: python3 level8_sg.py <orbit index 0..14 | all> [--fast]
"""
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "mod-s2-gamma4-index2-census-2026-09-17"))
import pbar  # noqa: E402
import exact_d  # noqa: E402
import index2 as X2  # noqa: E402

S = pbar.S
P = pbar.P
I4 = np.eye(4, dtype=np.int64)


def coset_action(mats, R, piv, chi):
    m8 = [A % 8 for A in mats]
    chi = np.array(chi, dtype=np.int64)
    lift = {}

    def key(A):
        k4 = X2.G.canon_pm(A % 4, 4)
        L = lift.get(k4)
        if L is None:
            lift[k4] = A.copy()
            return (k4, 0)
        X = (A @ X2.sinv(L, 8)) % 8
        if not ((X - I4) % 4 == 0).all():
            X = (-X) % 8
        return (k4, int(chi @ X2.coords(X2.y_of(X), R, piv)) % 2)

    index, reps, act = {key(I4.copy()): 0}, [I4.copy()], []
    q = 0
    while q < len(reps):
        A = reps[q]
        row = []
        for B in m8:
            nA = (A @ B) % 8
            k = key(nA)
            if k not in index:
                index[k] = len(reps)
                reps.append(nA)
            row.append(index[k])
        act.append(row)
        q += 1
    return act


def run(idx, chi, size, fast):
    t0 = time.time()
    rels = P.check_presentation()
    tw = P.standard_twists(P.conj_table())
    twists = [tuple(w) + tuple(w) for _, w in sorted(tw.items())]
    mats = pbar.pure_mats()
    for u, v in rels:
        assert pbar.is_pm_identity(pbar.word_mat(u, mats) @
                                   pbar.sinv(pbar.word_mat(v, mats)))
    assert pbar.is_pm_identity(pbar.word_mat(P.delta2_pure(), mats))
    for w in twists:
        assert (pbar.word_mat(w, mats) == I4).all()
    relators = list(rels) + [(P.delta2_pure(), ())]
    R = X2.gamma48_basis()
    piv = [int(np.nonzero(r)[0][0]) for r in R]
    act = coset_action(mats, R, piv, chi)
    assert len(act) == 1024, len(act)
    label = f"chi{idx}" + ("-fast" if fast else "")
    print(f"[{label}] chi={list(chi)} orbit {size}: Pbar cosets {len(act)}",
          flush=True)
    ngen, Rr, vs = pbar.rs(act, relators, twists, reduce_twists=fast)
    elim = None
    if fast:
        import fastelim
        elim = fastelim.eliminate
    out, (cols, H, keys, cls_of, B) = S.lattice_from_rs(
        ngen, Rr, vs, label, len(act), elim=elim)
    res = exact_d.certify(B, label)
    res.update(chi=list(chi), orbit_size=size, h1_rank=out.get("h1_rank"),
               h1_torsion=out.get("h1_torsion"), A_plus=out.get("A_plus"),
               seconds_total=round(time.time() - t0))
    return res


if __name__ == "__main__":
    fast = "--fast" in sys.argv[1:]
    which = [a for a in sys.argv[1:] if a != "--fast"][0]
    _, reps = X2.orbit_reps(X2.gamma48_basis())
    idxs = range(len(reps)) if which == "all" else [int(which)]
    results = []
    for i in idxs:
        chi, size = reps[i]
        results.append(run(i, chi, size, fast))
        name = "level8-" + which + ("-fast" if fast else "")
        json.dump(results, open(os.path.join(HERE, f"exact-{name}.json"), "w"),
                  indent=1)
    print("all SG:", all(r["short_generated"] for r in results), flush=True)
