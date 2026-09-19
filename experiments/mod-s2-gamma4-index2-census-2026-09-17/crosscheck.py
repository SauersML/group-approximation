#!/usr/bin/env python3
"""Compare lean_eliminate reruns (INDEX2_LEAN=1) with the census.unit_eliminate
results recorded in index2-results.json, orbit by orbit.

usage: crosscheck.py LEANDIR [OUT]   (OUT default: index2-lean-crosscheck.json)
"""
import json
import os
import sys

FIELDS = ["h1_rank", "h1_torsion", "classes", "class_coset_counts", "W_rank",
          "gcd_aug", "d_upper_exact_point", "theta_values", "cert_l1",
          "cert_aug", "cert_support", "chi", "orbit_size", "cosets"]


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    lean_dir = sys.argv[1]
    out = sys.argv[2] if len(sys.argv) > 2 else os.path.join(
        here, "index2-lean-crosscheck.json")
    ref = {r["orbit_index"]: r for r in
           json.load(open(os.path.join(here, "index2-results.json")))["orbits"]}
    rows = []
    for k in sorted(ref):
        p = os.path.join(lean_dir, f"orbit-{k}.json")
        if not os.path.exists(p):
            continue
        lean = json.load(open(p))[0]
        diff = {f: [ref[k].get(f), lean.get(f)] for f in FIELDS
                if ref[k].get(f) != lean.get(f)}
        rows.append({"orbit_index": k, "agree": not diff, "diff": diff,
                     "lean": lean})
    res = {"compared_orbits": [r["orbit_index"] for r in rows],
           "all_agree": all(r["agree"] for r in rows),
           "fields": FIELDS, "rows": rows}
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps({k: res[k] for k in ("compared_orbits", "all_agree")}))
    print([(r["orbit_index"], r["diff"]) for r in rows])


if __name__ == "__main__":
    main()
