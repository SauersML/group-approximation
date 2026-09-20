#!/usr/bin/env python3
"""Run level8_purebraid + level8_lattice for Gamma(2), Gamma(4) and one
representative of each of the 15 Sp_4(F_2)-orbits of index-two subgroups
Gamma'' of Gamma(4) containing Gamma(8).  Writes level8-results.json here.

Usage: python3 run_all.py SCRATCH_DIR
"""
import json
import os
import pickle
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import level8_index2 as L8  # noqa: E402
import level8_lattice as LL  # noqa: E402
import level8_purebraid as P  # noqa: E402


def main(scratch):
    basis, orbits = L8.functional_orbits()
    jobs = [("N2", None, 1), ("N4", None, 1)]
    jobs += [("f", o[0], len(o)) for o in orbits]
    out = os.path.join(HERE, "level8-results.json")
    results = json.load(open(out)) if os.path.exists(out) else {}
    for mode, code, size in jobs:
        name = mode if code is None else f"f{code}"
        if name in results:
            continue
        d = P.reduce_mode(mode, code)
        pk = os.path.join(scratch, f"pb-{name}.pkl")
        with open(pk, "wb") as fh:
            pickle.dump(d, fh)
        js = os.path.join(scratch, f"pb-{name}.json")
        LL.main(pk, js)
        r = json.load(open(js))
        r["mode"], r["orbit_size"] = mode, size
        r["cosets_in_K2"] = d["cosets_in_K2"]
        if code is not None:
            r["f_coords_in_JS_basis"] = [(code >> k) & 1 for k in range(10)]
        results[name] = r
        with open(out, "w") as fh:
            json.dump(results, fh, indent=1)
        print("DONE", name, r.get("d"), r.get("positive_aug10") is not None,
              flush=True)


if __name__ == "__main__":
    main(sys.argv[1])
