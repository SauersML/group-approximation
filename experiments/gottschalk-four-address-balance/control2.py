#!/usr/bin/env python3
"""Consistency control for the table-group triage (analyze3.json).

For every distinct minimal failing partition decided as a free product or graph product of cyclic
groups, rebuild the recognized normal form through a second entry point (dflip.make_nf, which runs its
own Nielsen search) and check:
  (1) every ORIGINAL relator of G_P is trivial in the recognized normal form, so the substitution
      tracking really defines a homomorphism from G_P;
  (2) the amenable flag and the memory-distinct flag agree with analyze3.json;
  (3) for partitions decided finite by coset enumeration, the order is re-derived with sympy's
      two strategies at a larger coset limit.
"""
import json, sys
import analyze2 as A
import dflip as D


def main():
    tri = json.load(open(sys.argv[1]))
    flip = json.load(open(sys.argv[2]))
    parts = [tuple(p) for p in flip["partitions"]]
    v = tri["verdict"]
    stats = {"checked_nf": 0, "relators_vanish": 0, "flags_agree": 0, "no_nf_second_path": 0,
             "finite_checked": 0, "finite_agree": 0, "other": 0}
    problems = []
    for k_s, ver in v.items():
        k = int(k_s)
        rels = A.relators(parts[k])
        form = ver["form"]
        if form in ("free-product-of-cyclics", "graph-product-of-cyclics", "trivial"):
            cls, nf = D.make_nf(rels)
            if nf is None:
                if cls.get("form") == "trivial" and ver.get("memory_distinct") is False:
                    stats["flags_agree"] += 1
                    continue
                stats["no_nf_second_path"] += 1
                problems.append((k, "no nf on second path", cls))
                continue
            stats["checked_nf"] += 1
            one = nf(())
            if all(nf(r) == one for r in rels):
                stats["relators_vanish"] += 1
            else:
                problems.append((k, "relator not trivial", ver))
            if cls.get("amenable") == ver.get("amenable") and cls.get("memory_distinct") == ver.get("memory_distinct"):
                stats["flags_agree"] += 1
            else:
                problems.append((k, "flag mismatch", cls, ver))
        elif form == "finite":
            stats["finite_checked"] += 1
            res = A.coset_decide(rels)
            if res.get("form") == "finite" and res.get("order") == ver.get("order"):
                stats["finite_agree"] += 1
            else:
                problems.append((k, "finite mismatch", res, ver))
        else:
            stats["other"] += 1
    print(json.dumps(stats))
    for p in problems[:40]:
        print("PROBLEM", json.dumps(p, default=str))


if __name__ == "__main__":
    main()
