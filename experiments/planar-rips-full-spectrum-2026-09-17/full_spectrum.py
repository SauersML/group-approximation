#!/usr/bin/env python3
"""Full-spectrum H_2 torsion of periodic Rips complexes.

For a periodic graph (k orbits, adj[i] = {(i2, s)}), compute the exact
F_p[t^{+-1}]-module torsion of H_2(R(Y); F_p) as coker(d_3) torsion, over
ALL eigenvalues lambda in the algebraic closure of F_p (not only +-1).
Also returns twisted Betti numbers at a random lambda (generic ranks).

periodic_rips.py (copied from experiments/planar-rips-periodic-strip-2026-09-17
on the swarm main branch) supplies cliques, boundary shifts, reduction.
"""
import random
import flint
from periodic_rips import cliques, boundary_entries, rank_mod_p, reduce_periodic, \
    periodic_graph_from_points, P
from laurent_smith import torsion_of_coker, factor_invariants


def laurent_rows(rows, p=P):
    out = []
    for row in rows:
        acc = {}
        for (c, sg, sh) in row:
            acc.setdefault(c, {})
            acc[c][sh] = (acc[c].get(sh, 0) + sg) % p
        prow = {}
        for c, d in acc.items():
            m = max(d)
            coeffs = [0] * (m + 1)
            for sh, x in d.items():
                coeffs[sh] = x
            f = flint.nmod_poly(coeffs, p)
            if not f.is_zero():
                prow[c] = f
        out.append(prow)
    return out


def h2_spectrum(k, adj, cap=None, p=P, seed=0):
    """Returns dict with sizes, generic betti b0..b2, H2 free rank, and the
    irreducible factors of the H2 torsion (all eigenvalues)."""
    cl = cliques(k, adj, 4)
    sizes = [len(cl[d]) for d in (1, 2, 3, 4)]
    if cap is not None and sizes[3] > cap:
        return {"sizes": sizes, "skipped": True}
    index = {d: {c: n for n, c in enumerate(cl[d + 1])} for d in range(4)}
    bnd = {d: boundary_entries(cl[d + 1], index[d - 1]) for d in (1, 2, 3)}
    lam = random.Random(seed).randrange(2, p - 1)
    rk = {d: rank_mod_p(bnd[d], sizes[d - 1], lam, p) for d in (1, 2, 3)}
    b = [sizes[0] - rk[1], sizes[1] - rk[1] - rk[2], sizes[2] - rk[2] - rk[3]]
    free, invs, residual = torsion_of_coker(laurent_rows(bnd[3], p), sizes[2], p)
    # free rank of coker d3 = rank H2 + rank B1 ; rank B1 = rk[2]
    h2_free = free - rk[2]
    return {"sizes": sizes, "generic_betti": b, "h2_free_rank": h2_free,
            "torsion": factor_invariants(invs), "residual": residual,
            "skipped": False}
