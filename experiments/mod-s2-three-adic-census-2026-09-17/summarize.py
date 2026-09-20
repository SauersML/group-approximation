#!/usr/bin/env python3
"""Tabulate local-orbit-<a>.json for the 16 classes of Y and derive b_1(M_9).

Checks, per orbit: c_m = 26 (so a_Y = 0, Step 3), the transfer check, the
class count (45 for n_Y = 0; for n_Y > 0 the 45 groups are the collapse of
Lemma C'), and reads rank W, gcd aug, cert l1 and d.  Writes
first-layer-results.json.
Usage: python3 summarize.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    orbs = json.load(open(os.path.join(HERE, "orbits.json")))
    rows, b1_9 = [], 24
    for a, o in enumerate(orbs):
        r = json.load(open(os.path.join(HERE, f"local-orbit-{a}.json")))
        size = o["size_with_sign"]
        ok = (r["c_m"] == 26 and not r["smaller_invariants"]
              and r["group_vectors_consistent"] and r["splittings_hit"] == 45
              and r["classes"] == 45)
        if r["n_Y"] == 0:
            ok = ok and r["transfer_check_3W3_in_L"] and r["W3_in_L"] \
                and r["index_in_W3_elementary_divisors"] == [] and r["exact"]
        else:
            ok = ok and r["transfer_W3_in_L"] and r["exact_3local"]
        a_Y = (r["c_m"] - 26) // 2      # exact when c_m = 26 (then 0)
        b1_9 += a_Y * size
        rows.append({"orbit": a, "size": size, "n_Y": r["n_Y"],
                     "true_classes": 45 + 2 * r["n_Y"], "c_m": r["c_m"],
                     "a_Y": a_Y, "rank_W": r["rank_W"],
                     "gcd_aug": r["gcd_aug_W"], "cert_l1": r["cert_l1"],
                     "distance": r["distance"], "checks_pass": ok})
        print(json.dumps(rows[-1]))
    out = {"modulus": 81, "orbits": rows, "b1_M9": b1_9,
           "all_checks_pass": all(x["checks_pass"] for x in rows)}
    print(json.dumps({"b1_M9": b1_9, "all_checks_pass": out["all_checks_pass"]}))
    with open(os.path.join(HERE, "first-layer-results.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
