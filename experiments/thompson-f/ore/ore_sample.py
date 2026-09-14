#!/usr/bin/env python3
"""Deterministic sample of P_(2,2) pairs settled by the census; produce explicit certificates for PL checking."""
import glob, json, random, sys
from ore_linalg import SETS
from ore_certify import certificate

task, ntask = int(sys.argv[1]), int(sys.argv[2])
S = SETS["S35"]
rnd = random.Random(20260913)
all_pairs = [(a, b) for a in range(1, 512) for b in range(1, 512) if a < b]
uns5 = set(map(tuple, json.load(open("s35_unsolved_after_k5.json"))["unsolved"]))
low = [p for p in all_pairs if p not in uns5]
solved67 = []
for f in sorted(glob.glob("s35_k7_shard*.json")):
    solved67 += json.load(open(f))["solved"]
d6 = sorted(s for s in solved67 if s[2] == 6)
d7 = sorted(s for s in solved67 if s[2] == 7)
sample = ([(a, b, None) for a, b in rnd.sample(low, 24)]
          + [(a, b, k) for a, b, k, N in rnd.sample(d6, 24)]
          + [(a, b, k) for a, b, k, N in rnd.sample(d7, 24)])
out = []
for a, b, k in sample[task::ntask]:
    for kk in ([k] if k is not None else range(1, 6)):
        r = certificate(S, a, b, kk, kk + 3)
        if r:
            u, v = r
            out.append({"S": [list(s) for s in S], "a": a, "b": b, "k": kk, "N": kk + 3, "u": u, "v": v})
            break
    else:
        raise SystemExit("no certificate %d %d %s" % (a, b, k))
json.dump(out, open("s35_sample_certs_%d.json" % task, "w"))
print(json.dumps({"task": task, "certs": len(out), "degrees": [c["k"] for c in out],
                  "max_terms": max(len(c["u"]) + len(c["v"]) for c in out)}))
