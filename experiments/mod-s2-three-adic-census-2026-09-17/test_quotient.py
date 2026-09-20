#!/usr/bin/env python3
"""Cross-check of the iota-quotient pipeline against census.py on subgroups
not containing -I (vec-3, frame-3 is too slow here): b1, torsion, number of
classes, rank W, gcd aug W and d must agree."""
import json
import sys

import threeadic
from threeadic import census

ORIG_RELATORS = census.relators


def via_quotient(name):
    census.relators = ORIG_RELATORS
    start, step = census.case(name)
    objs, act = census.enumerate_by_step(start, step)
    census.check_action(act)
    qact, orig = threeadic.quotient_table(act)
    census.relators = threeadic.relators_mod_iota
    census.check_action(qact)
    ngen, rels, vs = census.rs_data(qact)
    orep, _ = threeadic.stab_orbit_reps(qact)   # as in threeadic.run
    vs = [vs[c] for c in orep]
    cols, R, V = census.unit_eliminate(ngen, rels, vs)
    Rd, Vd = census.to_dense(R, cols), census.to_dense(V, cols)
    H = census.hnf_rows(Rd, len(cols)) if Rd else []
    b1, tors = census.h1_invariants(H, len(cols)) if H else (len(cols), [])
    classes = {}
    reps = []
    for c in range(len(orep)):
        key = census.reduce_mod_hnf(Vd[c], H)
        if key not in classes:
            classes[key] = len(classes)
            reps.append(c)
    B = census.w_lattice(H, [Vd[c] for c in reps], len(cols))
    g = 0
    for row in B:
        g = __import__("math").gcd(g, sum(row))
    dist = census.distance_milp(B)[0] if B else None
    census.relators = ORIG_RELATORS
    return {"b1": b1, "torsion": tors, "classes": len(reps),
            "rank_W": len(B), "gcd_aug_W": g, "distance": str(dist)}


def main(names):
    for name in names:
        census.relators = ORIG_RELATORS
        full = census.run(name)
        full = {k: full[k] for k in ("b1", "torsion", "classes", "rank_W",
                                     "gcd_aug_W", "distance")}
        q = via_quotient(name)
        print(json.dumps({"case": name, "full": full, "quotient": q,
                          "agree": full == q}), flush=True)


if __name__ == "__main__":
    main(sys.argv[1:] or ["vec-3", "vecpm-4"])
