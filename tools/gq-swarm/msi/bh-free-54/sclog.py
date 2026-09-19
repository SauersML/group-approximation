#!/usr/bin/env python3
"""Single-cut logging for the least-damage tree-domination recursion (request of bh-major-mcg-2, 36ab182de).
At every node C of the recursion with >= 2 fragments, and for every first split s of C, record:
  straddlers(s)     fragments crossing the plane of s
  single-cut(s)     every straddler is cut by that plane into exactly two cells (one edge split of the straddler)
  non-inherited(s)  fragments inside a child that do not descend from it
A node is SC if some first split is single-cut (vacuously if it has no straddler).  Nodes with no SC split are
reported with their dissection.  Instances: the named rank-3 instances, and restrictions to a first-split child of
cut-and-synchronized random split trees (ranks 3 and 4), as in td.py.  Calibration: rank 2 has no straddlers."""
import sys, json, time, random
sys.setrecursionlimit(100000)
import tdlib as T
from gen import cell, sub, isdesc, inv, resolve, sync_tree, is_tree, delta, rand_tree, Cap

T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 230.0
rnd = random.Random(4242)
T.G.rnd.seed(4242)
LOG = {"nodes": 0, "clean": 0, "sc": 0, "no_sc": 0, "dec": 0, "no_dec": 0, "dec_examples": [], "r2_choice_sc": 0, "max_straddlers": 0, "examples": []}
orig_choose = T.choose


def logged_choose(C, frags, rule):
    n = len(C)
    LOG["nodes"] += 1
    any_sc = any_clean = any_dec = False
    per = []
    for i in range(n):
        for j in range(i + 1, n):
            c1, c2 = T.children(C, i, j)
            A = inv(C)
            ell = tuple(A[i][k] - A[j][k] for k in range(n))
            strad = [f for f in frags if not sub(f, c1) and not sub(f, c2)]
            noninh = sum(1 for f in frags if (sub(f, c1) and not isdesc(f, c1)) or (sub(f, c2) and not isdesc(f, c2)))
            cutp = [resolve(f, ell) for f in strad]
            sc = all(len(x) == 2 for x in cutp)
            a = sum(1 for f in frags if sub(f, c1))
            b = sum(1 for f in frags if sub(f, c2))
            p1 = sum(1 for x in cutp for g in x if sub(g, c1))
            p2 = sum(1 for x in cutp for g in x if sub(g, c2))
            dec = noninh == 0 and a + p1 < len(frags) and b + p2 < len(frags)
            any_dec |= dec
            any_sc |= sc
            any_clean |= (not strad and not noninh)
            LOG["max_straddlers"] = max(LOG["max_straddlers"], len(strad))
            per.append(((i, j), len(strad), sc, noninh))
    s = orig_choose(C, frags, rule)
    LOG["clean"] += any_clean
    if any_dec:
        LOG["dec"] += 1
    else:
        LOG["no_dec"] += 1
        if len(LOG["dec_examples"]) < 3:
            LOG["dec_examples"].append({"C": C, "frags": sorted(frags)})
    if any_sc:
        LOG["sc"] += 1
    else:
        LOG["no_sc"] += 1
        if len(LOG["examples"]) < 3:
            LOG["examples"].append({"C": C, "frags": sorted(frags), "per_split": per})
    for (pair, ns, sc, ni) in per:
        if pair == tuple(s) and sc:
            LOG["r2_choice_sc"] += 1
    return s


T.choose = logged_choose


def instances(n, k):
    C = delta(n)
    U0 = rand_tree(C, k)
    i, j = sorted(rnd.sample(range(n), 2))
    c1, c2 = T.children(C, i, j)
    A = inv(C)
    ell = tuple(A[i][q] - A[j][q] for q in range(n))
    U1 = [x for p in U0 for x in resolve(p, ell)]
    U = []
    for p in U1:
        S = c1 if sub(p, c1) else c2
        U += [p] if isdesc(p, S) else sync_tree(p, S)
    return [(ch, [p for p in U if sub(p, ch)]) for ch in (c1, c2)]


e0, e1, e2 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
c, v01, v02, v12 = (1, 1, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1)
u, w, z = (2, 0, 1), (2, 1, 1), (2, 2, 1)
NAMED = {
    "Z": (delta(3), [cell([c, e1, e2]), cell([e0, c, e2]), cell([e0, e1, c])]),
    "M": (delta(3), [cell([e0, v01, v02]), cell([e1, v01, v12]), cell([e2, v02, v12]), cell([v01, v12, c]),
                     cell([v12, v02, c]), cell([v02, v01, c])]),
    "P9": (delta(3), [cell([e2, (0, 1, 1), (1, 0, 1)]), cell([e1, (0, 1, 1), c]), cell([e1, e0, (2, 0, 1)]),
                      cell([e1, c, (2, 0, 1)]), cell([(0, 1, 1), (1, 0, 1), (3, 0, 2)]), cell([(0, 1, 1), c, (2, 1, 2)]),
                      cell([(0, 1, 1), (2, 1, 2), (3, 0, 2)]), cell([c, (2, 0, 1), (3, 0, 2)]), cell([c, (2, 1, 2), (3, 0, 2)])]),
    "mcg2_restriction": (cell([e0, v01, e2]), [cell([e0, w, u]), cell([e0, z, w]), cell([e0, v01, z]), cell([u, w, v02]),
                                                cell([w, z, v02]), cell([z, c, v02]), cell([v02, c, e2])]),
}
res = {}
for name, (C, D) in NAMED.items():
    before = dict(LOG)
    s, st, Tr = T.run(C, D, "R2")
    res[name] = {"status": s, "nodes": LOG["nodes"] - before["nodes"], "no_sc": LOG["no_sc"] - before["no_sc"]}
print(json.dumps({"named": res, "log": {k: v for k, v in LOG.items() if k not in ("examples", "dec_examples")}}), flush=True)

for n, ks, frac in ((2, (4, 8, 16), 0.05), (3, (6, 10, 14, 20, 28, 36), 0.6), (4, (4, 6, 8, 10, 12, 14), 0.97)):
    stat = {"instances": 0, "non_tree": 0}
    for k in ks:
        for _ in range(500):
            if time.time() - T0 > frac * TL:
                break
            try:
                inst = instances(n, k)
            except (Cap, RuntimeError, RecursionError):
                continue
            for ch, D in inst:
                stat["instances"] += 1
                if is_tree(ch, D):
                    continue
                stat["non_tree"] += 1
                s, st, Tr = T.run(ch, D, "R2")
                stat[s] = stat.get(s, 0) + 1
    print(json.dumps({"rank": n, "stat": stat, "log": {k: v for k, v in LOG.items() if k not in ("examples", "dec_examples")},
                      "secs": round(time.time() - T0, 1)}), flush=True)
print(json.dumps({"no_sc_examples": LOG["examples"], "no_dec_examples": LOG["dec_examples"]}), flush=True)
