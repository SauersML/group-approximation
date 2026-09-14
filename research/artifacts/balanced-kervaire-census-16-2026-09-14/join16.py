"""Join the two coset-enumeration classifiers of the L = 16, 17 census by class id.

Inputs:
  census lines            "<id> <L> <r1> <r2>"
  GAP bal.g results       "<id> <L> <r1> <r2> <VERDICT> [<arg>] ms=<t>"
  tc_verify.py results    "<id> <r1> <r2> ORDER <n>" | "<id> <r1> <r2> OVERFLOW" | "<id> <r1> <r2> ERROR <msg>"
Checks that each census id occurs exactly once in each output with the same relators, then compares:
  - GAP TRIVIAL n=1 with tc ORDER 1, and GAP FINITE n=k with tc ORDER k: agreement (closed);
  - GAP QUOTIENT / SIMPLE / OPEN with tc OVERFLOW: agreement (neither closes a table);
  - a closed table on one side only: a budget difference, listed separately;
  - two closed tables of different orders, or tc ORDER 1 against a GAP finite quotient: contradiction.
Usage: join16.py CENSUS GAP TC
"""
import sys
from collections import Counter


def load_census(path):
    d = {}
    for ln in open(path):
        p = ln.split()
        if len(p) >= 4:
            d[p[0]] = (p[2], p[3])
    return d


def load(path, rel_at, verdict_at):
    d, dup = {}, 0
    for ln in open(path):
        p = ln.split()
        if len(p) <= verdict_at:
            continue
        if p[0] in d:
            dup += 1
        d[p[0]] = ((p[rel_at], p[rel_at + 1]), p[verdict_at:])
    return d, dup


def main():
    cen = load_census(sys.argv[1])
    gap, gdup = load(sys.argv[2], 2, 4)
    tc, tdup = load(sys.argv[3], 1, 3)
    stats = Counter()
    problems, budget = [], []
    for cid, rels in cen.items():
        g, t = gap.get(cid), tc.get(cid)
        if g is None or t is None:
            stats["missing"] += 1
            problems.append((cid, "missing", "gap" if g is None else "", "tc" if t is None else ""))
            continue
        if g[0] != rels or t[0] != rels:
            stats["relator-mismatch"] += 1
            problems.append((cid, "relators"))
            continue
        gv, tv = g[1][0], t[1][0]
        if tv == "ERROR":
            stats["tc-error"] += 1
            problems.append((cid, "tc-error", " ".join(t[1])))
            continue
        gorder = 1 if gv == "TRIVIAL" else (int(g[1][1].split("=")[1]) if gv == "FINITE" else None)
        torder = int(t[1][1]) if tv == "ORDER" else None
        if gorder is not None and torder is not None:
            if gorder == torder:
                stats["agree-closed"] += 1
            else:
                stats["contradiction"] += 1
                problems.append((cid, "orders", gorder, torder))
        elif gorder is None and torder is None:
            stats["agree-not-closed"] += 1
        elif torder is not None:
            if torder == 1 and gv in ("QUOTIENT", "SIMPLE"):
                stats["contradiction"] += 1
                problems.append((cid, "trivial-vs-quotient", gv))
            else:
                stats["budget-tc-closed-only"] += 1
                budget.append((cid, gv, "ORDER", torder))
        else:
            stats["budget-gap-closed-only"] += 1
            budget.append((cid, gv, tv))
    extra_g = len(set(gap) - set(cen))
    extra_t = len(set(tc) - set(cen))
    print("census", len(cen), "gap", len(gap), "tc", len(tc), "gap-dups", gdup, "tc-dups", tdup,
          "gap-extra", extra_g, "tc-extra", extra_t)
    print(dict(sorted(stats.items())))
    for pr in problems[:40]:
        print("PROBLEM", *pr)
    for b in budget[:40]:
        print("BUDGET", *b)
    clean = not problems and not gdup and not tdup and not extra_g and not extra_t
    print("JOIN CLEAN" if clean else "JOIN NOT CLEAN", "budget-differences", len(budget))


if __name__ == "__main__":
    main()
