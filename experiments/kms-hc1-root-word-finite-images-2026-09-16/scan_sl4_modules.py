#!/usr/bin/env python3
"""Scan 3 (2026-09-16): affine lifts of vertex-injective SL_4(F_p) images of Gamma_p.

Representations (found by search_vertex_injective.py, p=7, n=4, T=2):
  R1: a=I+E01, b=I+E20, c=I+E12+E23   (nilindex(rho(rs)-1)=3)
  R2: a=I+E01, b=I+E12, c=I+E12+E23   (nilindex 2)
plus any others passed on the command line are not supported (edit REPS).
For each module M: Sym^m(V) and dual for m=1..MMAX, permutation modules on
P^3(F_p) over F_l.  Prints dim Z^1(Gamma_p;M) and rank of delta -> delta(w_p).
Usage: scan_sl4_modules.py <p> <MMAX> [l1,l2,...]
"""
import itertools
import sys

import numpy as np

import kmslib as K
from kmslib import sym_power, perm_rep, normalize

p = int(sys.argv[1])
MMAX = int(sys.argv[2])
ells = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else []
n = 4


def elem(terms):
    M = np.eye(n, dtype=np.int64)
    for (i, j, e) in terms:
        M[i, j] = (M[i, j] + e) % p
    return M


REPS = {
    "R1": [elem([(0, 1, 1)]), elem([(2, 0, 1)]), elem([(1, 2, 1), (2, 3, 1)])],
    "R2": [elem([(0, 1, 1)]), elem([(1, 2, 1)]), elem([(1, 2, 1), (2, 3, 1)])],
}


def report(label, rep):
    rel = rep.check_relators(p)
    ok = all(rel.values())
    if not ok:
        print(label, "RELATOR FAILURE", flush=True)
        return None
    wtriv = rep.is_identity(K.root_word(p))
    dimZ, rk, *_ = K.root_word_translation_rank(rep, p)
    print(f"{label}: dim={rep.n} q={rep.q} rho(w)=I:{wtriv} dimZ1={dimZ} "
          f"rank(delta->delta(w))={rk}", flush=True)
    return rk


for name, mats in REPS.items():
    base = K.Rep(mats, p)
    print(name, "relators", all(base.check_relators(p).values()), flush=True)
    for m in range(1, MMAX + 1):
        S = [sym_power(g, m, p) for g in mats]
        report(f"{name} Sym^{m}", K.Rep(S, p))
        Sd = [K.mat_inv_mod(M, p).T % p for M in S]
        report(f"{name} Sym^{m} dual", K.Rep(Sd, p))
    if ells:
        vecs = [v for v in itertools.product(range(p), repeat=n) if any(v)]
        pts = sorted({normalize(v, p) for v in vecs})
        for ell in ells:
            report(f"{name} F_{ell}[P3 points]", perm_rep(mats, pts, p, ell, "pt"))
            report(f"{name} F_{ell}[P3 hyperplanes]", perm_rep(mats, pts, p, ell, "line"))
