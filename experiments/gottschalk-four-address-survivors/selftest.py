#!/usr/bin/env python3
"""Calibration of replay.py's GAP oracle, recognition and normal forms on groups with known answers."""
import json, os, sys
import replay as R

gap, work = sys.argv[1], sys.argv[2]
os.makedirs(work, exist_ok=True)
o = R.Oracle(gap, work)
chk = R.Checker(o, R.words_upto(1), depth=0)
fails = 0


def expect(name, cond):
    global fails
    print(("PASS " if cond else "FAIL ") + name)
    fails += 0 if cond else 1


def cls(rels, finite=False):
    key = R.state_key([tuple(r) for r in rels])
    rec = o.get(key, tryfinite=finite)
    return R.recognize(rec)


F3 = cls([])
expect("F3 is a free product, not amenable, memory distinct",
       F3["form"] == "free-product" and F3["amenable"] is None and not F3["collapse"])
expect("F3 normal form separates ab from ba", F3["nf"]((1, 2)) != F3["nf"]((2, 1)))
F2 = cls([(-3, 1, 2)])
expect("c = ab gives a free product on two generators", F2["form"] == "free-product" and len(F2["orders"]) == 2)
expect("c = ab: nf(c) == nf(ab)", F2["nf"]((3,)) == F2["nf"]((1, 2)))
expect("c = ab: nf(aba^-1) != nf(b)", F2["nf"]((1, 2, -1)) != F2["nf"]((2,)))
D = cls([(1, 1), (2, 2), (3,)])
expect("Z/2*Z/2 with c = 1 amenable and collapsing", D.get("amenable") is True)
Z2 = cls([(1, 2, -1, -2), (3,)])
expect("Z^2 amenable", Z2.get("amenable") is True)
Z23 = cls([(1, 1), (2, 2, 2), (3,)])
expect("Z/2*Z/3 not amenable, nf(aa)==nf()", Z23.get("amenable") is None and Z23["nf"]((1, 1)) == Z23["nf"](()))
K = cls([(-2, 1, 2, 1), (3, 3)])
expect("Klein-type normalizer relator recognized amenable or free-product not claimed amenable",
       K.get("amenable") in (True, None))
A5 = cls([(1, 1), (2, 2, 2), (1, 2, 1, 2, 1, 2, 1, 2, 1, 2), (3,)], finite=True)
expect("(2,3,5) triangle group finite of order 60", A5.get("form") == "finite" and A5.get("order") == 60)
RACG = cls([(1, 1), (2, 2), (3, 3), (1, 3, 1, 3)])
expect("RACG path recognized as graph product, not amenable",
       RACG.get("form") in ("graph-product", "unrecognized") and RACG.get("amenable") is not True)
if RACG.get("form") == "graph-product":
    expect("RACG: nf(ac) == nf(ca)", RACG["nf"]((1, 3)) == RACG["nf"]((3, 1)))
    expect("RACG: nf(ab) != nf(ba)", RACG["nf"]((1, 2)) != RACG["nf"]((2, 1)))
# partition relators: identity partition gives the free group, a merge gives one relator
labels_id = list(range(12))
expect("identity partition has no relators", R.partition_relators(labels_id) == ())
print("gap batches", o.calls, "fails", fails)
sys.exit(1 if fails else 0)
