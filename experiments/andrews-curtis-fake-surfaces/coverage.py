#!/usr/bin/env python3
"""coverage.py -- join the enumerator's class list with the certificates.
usage: coverage.py <t> <classes file> <certificate jsonl/.gz files ...>
Every certificate record is re-checked with acverify.check (standalone checker). A class is covered when some
record for (t, g, code) passes as 'stably-ac-trivial' or 'pi1-nontrivial'. Prints counts, lists uncovered
classes, and lists the pi1-nontrivial classes."""
import sys, json, gzip, collections
import acverify
t = int(sys.argv[1])
classes = set()
for line in open(sys.argv[2]):
    tt, g, code, ml = map(int, line.split())
    assert tt == t; classes.add((g, code))
best = {}; tally = collections.Counter()
for fn in sys.argv[3:]:
    for line in (gzip.open(fn, "rt") if fn.endswith(".gz") else open(fn)):
        d = json.loads(line)
        if "code" not in d or d.get("t") != t: continue
        key = (d["g"], d["code"])
        if key not in classes: tally["record-for-unknown-class"] += 1; continue
        if "cert" not in d and "a5" not in d and "perm" not in d: continue
        if best.get(key) == "stably-ac-trivial": continue
        res = acverify.check(d); tally["check:" + res] += 1
        if res in ("stably-ac-trivial", "pi1-nontrivial"):
            if best.get(key) != "stably-ac-trivial": best[key] = res
uncovered = sorted(classes - set(best))
kinds = collections.Counter(best.values())
print(json.dumps({"t": t, "classes": len(classes), "covered": len(best), "uncovered": len(uncovered),
                  "stably_ac_trivial": kinds["stably-ac-trivial"], "pi1_nontrivial": kinds["pi1-nontrivial"],
                  "checks": dict(tally)}))
for k in uncovered[:50]: print("UNCOVERED", t, *k)
for k, v in sorted(best.items()):
    if v == "pi1-nontrivial": print("PI1_NONTRIVIAL", t, *k)
