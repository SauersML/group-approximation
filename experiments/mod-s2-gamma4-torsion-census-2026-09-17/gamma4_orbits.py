#!/usr/bin/env python3
"""Fourth stage: symmetry of the level-4 relations.

The group H/K4 (61440 elements, H = Stab_6 Mod(S_{0,6})) acts on the 160
separating classes by conjugation: the class of the coset with matrix A goes
to the class of M(h) A.  We check this is well defined, then compute the orbits
of the pure part P/K4 = (Z/2)^9 (matrices = I mod 2) and of H/K4 on the 1024
transversal relations, and whether transversal + single-splitting relations
generate W.
"""
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
from flint import fmpz_mat  # noqa: E402
import gamma4_structure as S  # noqa: E402
from gamma4 import canon_pm  # noqa: E402


def main(pkl, out):
    n, H, classes, coset_class, objs = S.load(pkl)
    m = len(classes)
    index = {o: i for i, o in enumerate(objs)}
    mats = [np.array(o, dtype=np.int64).reshape(4, 4) for o in objs]

    def act(hA):
        perm = [None] * m
        for c, A in enumerate(mats):
            d = coset_class[index[canon_pm((hA @ A) % 4, 4)]]
            s = coset_class[c]
            assert perm[s] in (None, d), "conjugation not well defined"
            perm[s] = d
        return tuple(perm)

    G = [C.GENMATS[i] % 4 for i in range(4)]
    gens_H = [act(A) for A in G]
    # pure braid generators A_ij = s_{j-1}..s_{i+1} s_i^2 s_{i+1}^-1..s_{j-1}^-1
    Ginv = [np.round(np.linalg.inv(A.astype(float))).astype(np.int64) % 4
            for A in C.GENMATS[:4]]
    gens_P = []
    for i in range(4):
        for j in range(i + 1, 5):
            A = np.eye(4, dtype=np.int64)
            for k in range(j - 1, i, -1):
                A = A @ G[k]
            A = A @ G[i] @ G[i]
            for k in range(i + 1, j):
                A = A @ Ginv[k]
            gens_P.append(act(A % 4))
    Pg, Hg = closure(gens_P), closure(gens_H)
    print("pure / H image orders on classes:", len(Pg), len(Hg), flush=True)
    rels = transversal(n, H, classes, coset_class, objs)
    relset = {tuple(sorted(r)) for r in rels}
    orbitsP = orbits(relset, Pg)
    orbitsH = orbits(relset, Hg)
    print("transversal relations", len(relset), "P-orbit sizes",
          sorted(len(o) for o in orbitsP), "H-orbits", len(orbitsH), flush=True)
    res = {"pure_group_order_on_classes": len(Pg),
           "H_group_order_on_classes": len(Hg),
           "transversal": len(relset),
           "P_orbit_sizes": sorted(len(o) for o in orbitsP),
           "H_orbit_sizes": sorted(len(o) for o in orbitsH)}
    json.dump(res, open(out, "w"), indent=1)
    return res


def closure(gens):
    idt = tuple(range(len(gens[0])))
    seen = {idt}
    frontier = [idt]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(g[p[i]] for i in range(len(p)))
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
        frontier = nxt
    return seen


def orbits(relset, group):
    left, out = set(relset), []
    while left:
        r = left.pop()
        orb = {tuple(sorted(p[c] for c in r)) for p in group}
        assert orb <= relset | {r}, "group does not preserve relations"
        left -= orb
        out.append(orb)
    return out


def transversal(n, H, classes, coset_class, objs):
    m = len(classes)
    lab = S.class_splittings(coset_class, objs, m)[0]
    over = [[c for c in range(m) if lab[c] == s] for s in range(10)]
    K = S.phi_matrix(H, n)
    Phi = np.array([K @ np.array(v, dtype=np.int64) for v in classes])
    Ls, Lc = S.half_sums([Phi[o] for o in over[:5]])
    Rs, Rc = S.half_sums([Phi[o] for o in over[5:]])
    table = {}
    for i, row in enumerate(Ls):
        table.setdefault(row.tobytes(), []).append(i)
    rels = []
    for j, row in enumerate(-Rs):
        for i in table.get(row.tobytes(), []):
            ch = list(Lc[i]) + list(Rc[j])
            rels.append([over[g][c] for g, c in enumerate(ch)])
    return rels


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
