#!/usr/bin/env python3
"""Collect the per-orbit outputs of index2.py into index2-results.json.

usage: combine.py INDIR [OUT]

Also evaluates b_1(M_8) by the character decomposition
    H_1(M_8; C) = sum over chi in Hom(Gamma(4)/Gamma(8), C^*) of H_1(M_4; C_chi),
    b_1(M_chi) = b_1(M_4) + dim H_1(M_4; C_chi)   (chi != 1),
so b_1(M_8) = b_1(M_4) + sum_orbits |orbit| (b_1(M_chi) - b_1(M_4)).
"""
import json
import os
import sys
from fractions import Fraction

B1_M4 = 54
ORBIT_SIZES = [60, 15, 45, 20, 180, 180, 60, 60, 120, 90, 10, 6, 90, 72, 15]


def main():
    indir = sys.argv[1]
    here = os.path.dirname(os.path.abspath(__file__))
    out = sys.argv[2] if len(sys.argv) > 2 else os.path.join(
        here, "index2-results.json")
    rows = []
    for k in range(len(ORBIT_SIZES)):
        p = os.path.join(indir, f"orbit-{k}.json")
        if not os.path.exists(p):
            print("missing orbit", k)
            continue
        r = json.load(open(p))[0]
        assert r["orbit_index"] == k and r["orbit_size"] == ORBIT_SIZES[k]
        rows.append(r)
    done = len(rows) == len(ORBIT_SIZES)
    assert sum(ORBIT_SIZES) == 2 ** 10 - 1
    summary = {"orbits_done": len(rows), "orbits_total": len(ORBIT_SIZES),
               "subgroups_covered": sum(r["orbit_size"] for r in rows)}
    lo = [Fraction(1, 3 * r["cert_l1"]) for r in rows
          if r["cert_aug"] % 3 != 0]
    hi = [Fraction(r["d_upper_exact_point"]) for r in rows]
    summary["min_certified_lower_bound"] = str(min(lo)) if lo else None
    summary["max_upper_bound"] = str(max(hi)) if hi else None
    summary["all_d_equal_1_30"] = all(
        Fraction(1, 3 * r["cert_l1"]) == Fraction(1, 30) == Fraction(
            r["d_upper_exact_point"]) and r["cert_aug"] % 3 != 0 for r in rows)
    summary["b1_values"] = sorted({r["h1_rank"] for r in rows})
    if done:
        summary["b1_M8"] = B1_M4 + sum(r["orbit_size"] * (r["h1_rank"] - B1_M4)
                                       for r in rows)
    summary["torsion_by_orbit"] = {r["orbit_index"]: r["h1_torsion"]
                                   for r in rows}
    summary["classes_by_orbit"] = {r["orbit_index"]: r["classes"]
                                   for r in rows}
    json.dump({"summary": summary, "orbits": rows}, open(out, "w"), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
