#!/usr/bin/env python3
"""Orbit-algebra structure of the delta(3) instance.

Computes, for G = SL_3(Z/8) acting on X = (Z/8)^3 (512 points):
  - number of G-orbits on X x X  (= dim rho(G)', the witness algebra);
  - commutativity of the orbit algebra (multiplicity-free <=> abelian
    commutant <=> K is a phase vector: maximal phase locking);
  - same for the target parahoric Q1 = <e12(1), e13(1), e23(1),
    e21(2), e31(4), e32(2)> (= dim of the twisted commutant B').
"""
import json
import sys

import numpy as np

MOD = 8
D = MOD ** 3


def m(*r):
    return [list(r[0:3]), list(r[3:6]), list(r[6:9])]


def perm_of(g):
    p = np.empty(D, dtype=np.int64)
    for x0 in range(MOD):
        for x1 in range(MOD):
            for x2 in range(MOD):
                v0 = (g[0][0] * x0 + g[0][1] * x1 + g[0][2] * x2) % MOD
                v1 = (g[1][0] * x0 + g[1][1] * x1 + g[1][2] * x2) % MOD
                v2 = (g[2][0] * x0 + g[2][1] * x1 + g[2][2] * x2) % MOD
                p[(x0 * MOD + x1) * MOD + x2] = (v0 * MOD + v1) * MOD + v2
    return p


GENS_G = [m(1, 1, 0, 0, 1, 0, 0, 0, 1), m(1, 0, 0, 1, 1, 0, 0, 0, 1),
          m(1, 0, 1, 0, 1, 0, 0, 0, 1), m(1, 0, 0, 0, 1, 0, 1, 0, 1),
          m(1, 0, 0, 0, 1, 1, 0, 0, 1), m(1, 0, 0, 0, 1, 0, 0, 1, 1)]
GENS_Q1 = [m(1, 1, 0, 0, 1, 0, 0, 0, 1), m(1, 0, 1, 0, 1, 0, 0, 0, 1),
           m(1, 0, 0, 0, 1, 1, 0, 0, 1), m(1, 0, 0, 2, 1, 0, 0, 0, 1),
           m(1, 0, 0, 0, 1, 0, 4, 0, 1), m(1, 0, 0, 0, 1, 0, 0, 2, 1)]


def orbits_on_pairs(perms):
    n = D * D
    parent = np.arange(n, dtype=np.int64)

    def find(a):
        root = a
        while parent[root] != root:
            root = parent[root]
        while parent[a] != root:
            parent[a], a = root, parent[a]
        return root

    for p in perms:
        # pair (x, y) -> (p[x], p[y]);  index = x*D + y
        for x in range(D):
            px = p[x] * D
            xD = x * D
            for y in range(D):
                a = find(xD + y)
                b = find(px + p[y])
                if a != b:
                    parent[a] = b
    # one more sweep to ensure closure under the group (generators only
    # generate; iterate until stable)
    changed = True
    while changed:
        changed = False
        for p in perms:
            for x in range(D):
                px = p[x] * D
                xD = x * D
                for y in range(D):
                    a = find(xD + y)
                    b = find(px + p[y])
                    if a != b:
                        parent[a] = b
                        changed = True
    roots = set()
    for i in range(n):
        roots.add(find(i))
    labels = {r: k for k, r in enumerate(sorted(roots))}
    lab = np.empty(n, dtype=np.int64)
    for i in range(n):
        lab[i] = labels[find(i)]
    return len(roots), lab


def commutativity(lab, nor):
    # orbit matrices A_i: A_i[x, y] = 1 iff label(x*D+y) == i
    L = lab.reshape(D, D)
    mats = []
    for i in range(nor):
        mats.append((L == i).astype(np.float64))
    bad = 0
    for i in range(nor):
        Ai = mats[i]
        for j in range(i + 1, nor):
            Pij = Ai @ mats[j]
            Pji = mats[j] @ Ai
            if not np.allclose(Pij, Pji, atol=1e-9):
                bad += 1
    return bad


def main():
    out = {}
    for name, gens in (("G", GENS_G), ("Q1", GENS_Q1)):
        perms = [perm_of(g) for g in gens]
        nor, lab = orbits_on_pairs(perms)
        bad = commutativity(lab, nor) if nor <= 120 else -1
        out[name] = {"orbits_on_pairs": int(nor),
                     "noncommuting_orbit_pairs": int(bad)}
        print(json.dumps({name: out[name]}), flush=True)
    with open("sl3_orbit_algebra.json", "w") as f:
        json.dump(out, f, indent=1)
    print("DONE", file=sys.stderr)


if __name__ == "__main__":
    main()


def mult_profile(perms, nor, lab, tag):
    """Generic-element spectrum: eigenvalue multiplicities of a random
    self-adjoint orbit-algebra element recover the (mult, dim) profile:
    each irrep block contributes mult eigenvalues of multiplicity dim."""
    rng = np.random.default_rng(4242)
    L = lab.reshape(D, D)
    A = np.zeros((D, D))
    for i in range(nor):
        c = rng.normal()
        A += c * (L == i)
    A = (A + A.T) / 2.0
    ev = np.linalg.eigvalsh(A)
    ev = np.sort(ev)
    groups = []
    cur = [ev[0]]
    for e in ev[1:]:
        if abs(e - cur[-1]) < 1e-7:
            cur.append(e)
        else:
            groups.append(len(cur))
            cur = [e]
    groups.append(len(cur))
    from collections import Counter
    prof = Counter(groups)  # {dim: count over (irrep, mult-slot)}
    # dim d appearing c times means: irreps of dimension d contribute
    # total multiplicity c (sum of m over irreps of that dim)
    return {int(k): int(v) for k, v in sorted(prof.items())}


def main2():
    out = json.load(open("sl3_orbit_algebra.json"))
    for name, gens in (("G", GENS_G), ("Q1", GENS_Q1)):
        perms = [perm_of(g) for g in gens]
        nor, lab = orbits_on_pairs(perms)
        prof = mult_profile(perms, nor, lab, name)
        out[name]["generic_eig_profile_dim_to_totalmult"] = prof
        print(json.dumps({name: prof}), flush=True)
    with open("sl3_orbit_algebra.json", "w") as f:
        json.dump(out, f, indent=1)
    print("DONE2", file=sys.stderr)


main2()


def pairing_weights():
    """For each G-isotypic block, the Q1-profile of its compression:
    the pairing table the phase-locking floor consumes."""
    rng = np.random.default_rng(31)
    permsG = [perm_of(g) for g in GENS_G]
    norG, labG = orbits_on_pairs(permsG)
    LG = labG.reshape(D, D)
    A = np.zeros((D, D))
    for i in range(norG):
        A += rng.normal() * (LG == i)
    A = (A + A.T) / 2.0
    ev, U = np.linalg.eigh(A)
    # group eigenvalues -> G-isotypic projectors (block = irrep copy
    # cluster: eigenvalue multiplicity = dim of irrep; same-block
    # eigenvalues from same irrep have SAME dim; collect clusters)
    clusters = []
    start = 0
    for i in range(1, D + 1):
        if i == D or abs(ev[i] - ev[i - 1]) > 1e-7:
            clusters.append((start, i))
            start = i
    permsQ = [perm_of(g) for g in GENS_Q1]
    norQ, labQ = orbits_on_pairs(permsQ)
    LQ = labQ.reshape(D, D)
    B = np.zeros((D, D))
    for i in range(norQ):
        B += rng.normal() * (LQ == i)
    B = (B + B.T) / 2.0
    # G-isotypic projector = sum of clusters with same dim belonging
    # to one irrep: approximate: treat each ISOTYPIC component as the
    # span of all eigenvectors whose cluster size = that dim, grouped
    # by commuting-block structure.  Simplest robust move: compress B
    # to each eigen-CLUSTER (one irrep copy each) and report its
    # Q1-generic spectrum profile.
    out = []
    for (s0, s1) in clusters:
        W = U[:, s0:s1]
        Bc = W.T @ B @ W
        Bc = (Bc + Bc.T) / 2.0
        evc = np.sort(np.linalg.eigvalsh(Bc))
        groups = []
        cur = 1
        for i in range(1, len(evc)):
            if abs(evc[i] - evc[i - 1]) < 1e-6:
                cur += 1
            else:
                groups.append(cur)
                cur = 1
        groups.append(cur)
        from collections import Counter
        out.append({"g_block_dim": s1 - s0,
                    "q1_spectrum_profile": dict(Counter(groups))})
    with open("sl3_pairing_weights.json", "w") as f:
        json.dump(out, f, indent=1)
    from collections import Counter as C2
    agg = C2()
    for rec in out:
        agg[rec["g_block_dim"]] += 1
    print(json.dumps({"clusters_by_dim": dict(agg)}), flush=True)
    for rec in out[:12]:
        print(json.dumps(rec), flush=True)
    print("DONE3", file=sys.stderr)


pairing_weights()
