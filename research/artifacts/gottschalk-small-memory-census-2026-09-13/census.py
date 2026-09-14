#!/usr/bin/env python3
"""Exact small-memory census for Gottschalk's conjecture via rectangle clauses.

By `surjunctivity-is-axiomatized-by-rectangle-clauses`, the clause rho_D for strict
data D = (mu, nu, T_f, T_r) holds in every group iff it holds in the forward-relation
group P(T_f). Write T_r^P for the reverse table realized in P(T_f). Then:

  every group satisfies rho_D for all D with memories (S, M) and alphabet A
    <=>  for every closed forward table T_f and every pair (mu, nu) with Dec(T_f),
         Enc(T_r^P) holds.

(If Enc(T_r^P) fails for some Dec-solution, D = (mu, nu, T_f, T_r^P) is strict and
realized in P(T_f), so P(T_f) is not surjunctive. Conversely Enc at the finer table
T_r^P gives Enc at every coarser T_r, and strictness needs a T_r not containing T_r^P.)

nu is unconstrained off the tuples of relay outputs reachable under Dec, so the check
for a fixed mu asks whether ANY extension nu of the forced partial decoder nu_0 breaks
Enc(T_r^P) on some T_r^P-constant configuration q.

Input: tables.jsonl (from enum_tables.py) and oracle.jsonl with, per id,
  {"id", "fwd_classes": [[cell,...],...], "rev_classes": [[cell,...],...],
   "labels_distinct": bool, "resolved": bool}
Output: summary JSON and any counterexample candidates.
"""
import itertools, json, sys
import numpy as np

def load(path):
    return {r["id"]: r for r in map(json.loads, open(path))}

def census(tables, oracle, q):
    stats = {"tables": 0, "closed": 0, "degenerate": 0, "unresolved": 0,
             "dec_pairs": 0, "mus_with_dec": 0, "candidates": []}
    for tid, t in tables.items():
        stats["tables"] += 1
        o = oracle.get(tid)
        if o is None or not o.get("resolved", False):
            stats["unresolved"] += 1
            continue
        if not o["labels_distinct"]:
            stats["degenerate"] += 1
            continue
        ns, nm = t["ns"], t["nm"]
        S = ["1"] + [f"s{i}" for i in range(1, ns)]
        M = ["1"] + [f"m{i}" for i in range(1, nm)]
        # closedness: the realized forward partition must equal the input partition
        inp = sorted(sorted(b) for b in blocks_from_rels(t, S, M))
        real = sorted(sorted(b) for b in o["fwd_classes"])
        if inp != real:
            continue
        stats["closed"] += 1
        fcls = {c: i for i, b in enumerate(o["fwd_classes"]) for c in b}
        rcls = {c: i for i, b in enumerate(o["rev_classes"]) for c in b}
        cf, cr = len(o["fwd_classes"]), len(o["rev_classes"])
        # all forward assignments p in A^cf
        P = np.array(list(itertools.product(range(q), repeat=cf)), dtype=np.int64)
        # row index of relay s: sum over m of p(class(s,m)) * q^pos
        rows = np.zeros((P.shape[0], ns), dtype=np.int64)
        for si, s in enumerate(S):
            for mi, m in enumerate(M):
                rows[:, si] = rows[:, si] * q + P[:, fcls[f"{s}|{m}"]]
        demand = P[:, fcls["1|1"]]
        # reverse assignments
        Q = np.array(list(itertools.product(range(q), repeat=cr)), dtype=np.int64)
        zrows = np.zeros((Q.shape[0], nm), dtype=np.int64)
        for mi, m in enumerate(M):
            for si, s in enumerate(S):
                zrows[:, mi] = zrows[:, mi] * q + Q[:, rcls[f"{m}|{s}"]]
        rdemand = Q[:, rcls["1|1"]]
        nrules = q ** (q ** nm)
        powq_s = q ** ns
        for code in range(nrules):
            mu = np.array([(code // q ** i) % q for i in range(q ** nm)], dtype=np.int64)
            y = mu[rows]                       # relay outputs per assignment
            ycode = np.zeros(P.shape[0], dtype=np.int64)
            for si in range(ns):
                ycode = ycode * q + y[:, si]
            lo = np.full(powq_s, q, dtype=np.int64)
            hi = np.full(powq_s, -1, dtype=np.int64)
            np.minimum.at(lo, ycode, demand)
            np.maximum.at(hi, ycode, demand)
            reach = hi >= 0
            if np.any(lo[reach] != hi[reach]):
                continue                        # Dec fails for every nu
            stats["mus_with_dec"] += 1
            nu0 = np.where(reach, lo, -1)
            vals = nu0[zrows]                   # -1 marks a free decoder value
            free_rows = np.any(vals < 0, axis=1)
            # rows with no free value: direct check
            fixed = ~free_rows
            if np.any(fixed):
                idx = np.zeros(int(fixed.sum()), dtype=np.int64)
                for mi in range(nm):
                    idx = idx * q + vals[fixed, mi]
                if np.any(mu[idx] != rdemand[fixed]):
                    stats["candidates"].append({"table": tid, "mu": code, "kind": "fixed"})
                    continue
            broke = False
            for qi in np.nonzero(free_rows)[0]:
                keys = sorted({int(zrows[qi, mi]) for mi in range(nm) if vals[qi, mi] < 0})
                for assign in itertools.product(range(q), repeat=len(keys)):
                    a = dict(zip(keys, assign))
                    v = [int(vals[qi, mi]) if vals[qi, mi] >= 0 else a[int(zrows[qi, mi])]
                         for mi in range(nm)]
                    ix = 0
                    for x in v:
                        ix = ix * q + x
                    if mu[ix] != rdemand[qi]:
                        stats["candidates"].append({"table": tid, "mu": code, "kind": "free",
                                                    "q": Q[qi].tolist(), "nu_free": a})
                        broke = True
                        break
                if broke:
                    break
    return stats

def blocks_from_rels(t, S, M):
    # rebuild the input partition from the relator spanning trees
    cells = [f"{s}|{m}" for s in S for m in M]
    word = {k: tuple(v) for k, v in t["fwd"].items()}
    parent = {c: c for c in cells}
    def find(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c
    wmap = {}
    for c in cells:
        wmap.setdefault(word[c], []).append(c)
    for a, b in t["rels"]:
        ca = wmap[tuple(a)][0]; cb = wmap[tuple(b)][0]
        parent[find(ca)] = find(cb)
    groups = {}
    for c in cells:
        groups.setdefault(find(c), []).append(c)
    return list(groups.values())

if __name__ == "__main__":
    tables = load(sys.argv[1])
    oracle = load(sys.argv[2])
    q = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    st = census(tables, oracle, q)
    out = sys.argv[4] if len(sys.argv) > 4 else "census_summary.json"
    json.dump(st, open(out, "w"), indent=1)
    print(json.dumps({k: (v if k != "candidates" else len(v)) for k, v in st.items()}))
