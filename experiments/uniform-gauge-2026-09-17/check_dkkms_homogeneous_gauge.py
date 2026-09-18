#!/usr/bin/env python3
"""Checks for dkkms-affine-view-verifiers-any-sigma-sound-at-2c-1, part (D).

Reuses the instance builder of
experiments/dkkms-coarsening-2026-09-17/check_dkkms_coarsening.py (folded DKKMS
instances from UNSATISFIABLE 3LIN, k = 2) and checks the homogeneous gauge:

  (D1) pi_Q(r) = R_Q-component of r in R_Q + H_U does not depend on the member
       U of the class used, and pi_Q restricted to M is a bijection M -> R_Q;
  (D2) for random functionals psi_Q on the dimension-m representatives R_Q,
       G_psi(C, M)(r) = psi_Q(pi_Q(r)) satisfies the HOMOGENEOUS constraint of
       every exact triple on derived 2-to-2 edges: G(C1,M1)(r_1 x) = G(C2,M2)(r_2 x)
       for x in N;
  (D3) F* + G_psi satisfies every exact triple (value 1), for every psi tried;
  (D4) as psi_Q ranges over Fun(R_Q), G_psi(C, M) takes every functional on M
       equally often (uniform marginal at every coarsening vertex seen);
  (CTL) control: choosing psi independently per coarsening vertex instead of
       per folding class breaks the homogeneous constraint on some triples.
Run: python3 check_dkkms_homogeneous_gauge.py [--seed S] [--l L] [--psis P]
"""
import argparse
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "dkkms-coarsening-2026-09-17"))
import check_dkkms_coarsening as dk  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260917)
    ap.add_argument("--n", type=int, default=12)
    ap.add_argument("--eqs", type=int, default=8)
    ap.add_argument("--l", type=int, default=2)
    ap.add_argument("--bvertices", type=int, default=300)
    ap.add_argument("--pairs", type=int, default=6)
    ap.add_argument("--psis", type=int, default=8)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    k, ell = 2, args.l
    fails = []
    for _ in range(200):
        eqs, b = dk.make_instance(rng, args.n, args.eqs)
        legit = dk.legit_tuples(eqs, k)
        if len(eqs) == args.eqs and 6 <= len(legit) <= 16:
            break
    else:
        print("could not generate instance")
        return 2
    if not dk.unsatisfiable(args.n, eqs, b):
        fails.append("3LIN instance is satisfiable")
    blocks = [dk.Block(U, eqs, b) for U in legit]
    subs, cls_of, rep = {}, {}, {}
    for d in range(1, ell + 1):
        subs[d] = [blk.subspaces(d) for blk in blocks]
        classes = dk.folding_classes(blocks, subs[d])
        cls_of[d], rep[d] = dk.representatives(blocks, classes, fails, "dim %d" % d)
    class_blocks = {}
    for (w, L), c in cls_of[ell].items():
        class_blocks.setdefault(c, set()).add(w)

    gauge_cache, pi_cache = {}, {}

    def gauge(c, M):
        """F*(C, M) as in the DKKMS coarsening check."""
        key = (c, M)
        if key not in gauge_cache:
            u = min(class_blocks[c])
            m = dk.dim_of(M)
            Q = cls_of[m][(u, M)]
            RQ = rep[m][Q][1]
            gauge_cache[key] = {r: blocks[u].h[dk.decompose(RQ, blocks[u], r)[1]] for r in M}
        return gauge_cache[key]

    def pi(c, M):
        """(Q, {r: pi_Q(r)}) for r in M; checks (D1)."""
        key = (c, M)
        if key in pi_cache:
            return pi_cache[key]
        m = dk.dim_of(M)
        maps, Qs = set(), set()
        for u in sorted(class_blocks[c]):
            Q = cls_of[m][(u, M)]
            RQ = rep[m][Q][1]
            Qs.add(Q)
            maps.add(tuple(dk.decompose(RQ, blocks[u], r)[0] for r in sorted(M)))
        if len(Qs) != 1 or len(maps) != 1:
            fails.append("D1: pi_Q depends on the member U")
        Q = min(Qs)
        img = dict(zip(sorted(M), sorted(maps)[0]))
        if len(set(img.values())) != len(M) or set(img.values()) != set(rep[m][Q][1]):
            fails.append("D1: pi_Q is not a bijection M -> R_Q")
        pi_cache[key] = (m, Q, img)
        return pi_cache[key]

    psis = []
    for _ in range(args.psis):
        table = {}

        def psi(m, Q, v, table=table):
            if (m, Q) not in table:
                table[(m, Q)] = rng.choice(dk.functionals(rep[m][Q][1]))
            return table[(m, Q)][v]
        psis.append(psi)

    stats = dict(edges=0, exact=0, hom_violations=0, full_violations=0, vertices=0,
                 nonuniform=0, control_violations=0)
    seen_vertices = set()
    bverts = set()
    for blk in blocks:
        for Vm in dk.v_choices(blk, eqs):
            XV = dk.span([1 << x for x in range(args.n) if Vm >> x & 1])
            for Lp in dk.all_subspaces(XV, ell - 1):
                bverts.add((Vm, Lp))
    bverts = sorted(bverts, key=lambda t: (t[0], sorted(t[1])))
    rng.shuffle(bverts)
    used = 0
    for Vm, Lp in bverts:
        if used >= args.bvertices:
            break
        nbrs = [(w, L) for w, blk in enumerate(blocks) if dk.derivable(Vm, blk, eqs)
                for L in subs[ell][w] if Lp <= L]
        pairs = [(z1, z2) for z1 in nbrs for z2 in nbrs if z1 != z2]
        if not pairs:
            continue
        used += 1
        for z1, z2 in rng.sample(pairs, min(args.pairs, len(pairs))):
            stats["edges"] += 1
            sides = []
            for (w, L) in (z1, z2):
                c = cls_of[ell][(w, L)]
                R = rep[ell][c][1]
                blk = blocks[w]
                sides.append((c, R, blk, {x: dk.decompose(R, blk, x) for x in Lp}))
            for N in dk.all_subspaces(Lp):
                # Lemma B: exact pairs are exactly (r_1 N, r_2 N)
                M = [frozenset(s[3][x][0] for x in N) for s in sides]
                stats["exact"] += 1
                pis = [pi(s[0], Mi) for s, Mi in zip(sides, M)]
                gs = [gauge(s[0], Mi) for s, Mi in zip(sides, M)]
                for s, Mi in zip(sides, M):
                    if (s[0], Mi) not in seen_vertices:
                        seen_vertices.add((s[0], Mi))
                for psi in psis:
                    hom_bad = full_bad = False
                    for x in N:
                        vals_h, vals_f = [], []
                        for s, (m, Q, img), g in zip(sides, pis, gs):
                            q, dd = s[3][x]
                            G = psi(m, Q, img[q])
                            vals_h.append(G)
                            vals_f.append(g[q] ^ G ^ s[2].h[dd])
                        hom_bad |= vals_h[0] != vals_h[1]
                        full_bad |= vals_f[0] != vals_f[1]
                    stats["hom_violations"] += hom_bad
                    stats["full_violations"] += full_bad
                # control: an independent psi per coarsening vertex (not per
                # folding class) must break the homogeneous constraint sometimes
                ctl = {}
                for x in N:
                    vals = []
                    for s, Mi, (m, Q, img) in zip(sides, M, pis):
                        key = (s[0], Mi)
                        if key not in ctl:
                            ctl[key] = rng.choice(dk.functionals(rep[m][Q][1]))
                        vals.append(ctl[key][img[s[3][x][0]]])
                    if vals[0] != vals[1]:
                        stats["control_violations"] += 1
                        break
    # (D4) uniform marginals: enumerate psi_Q over Fun(R_Q) at each seen vertex
    for (c, M) in sorted(seen_vertices, key=lambda t: (t[0], sorted(t[1]))):
        m, Q, img = pi(c, M)
        counts = {}
        for f in dk.functionals(rep[m][Q][1]):
            key = tuple(f[img[r]] for r in sorted(M))
            counts[key] = counts.get(key, 0) + 1
        stats["vertices"] += 1
        if len(counts) != 2 ** m or len(set(counts.values())) != 1:
            stats["nonuniform"] += 1
    print("stats", stats)
    if stats["hom_violations"]:
        fails.append("D2: homogeneous gauge violates an exact triple")
    if stats["full_violations"]:
        fails.append("D3: F* + G_psi violates an exact triple")
    if stats["nonuniform"]:
        fails.append("D4: non-uniform marginal")
    if stats["control_violations"] == 0:
        fails.append("control degenerate: per-vertex psi never fails")
    if stats["exact"] == 0:
        fails.append("degenerate: no exact triples")
    print("failures:", len(fails))
    for f in fails[:20]:
        print("  FAIL", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
