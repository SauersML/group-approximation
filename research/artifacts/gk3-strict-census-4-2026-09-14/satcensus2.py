#!/usr/bin/env python3
"""Second, independent SAT encoding of strict rectangle data (encoding B).

Same question as satcensus.py: at a realized forward partition T_f of S x M and realized reverse
partition T_r of M x S, do rules mu: A^M -> A and nu: A^S -> A exist with Dec(T_f) and not Enc(T_r)?

Differences from encoding A, on purpose:
- symbols are binary-coded with ceil(log2 q) bits, invalid codes excluded by clauses;
- tables are keyed by symbol tuples through dictionaries, not by integer indices;
- Dec is imposed per assignment of the forward classes with no deduplication;
- realized pairs are read and deduplicated with frozensets by separate code;
- the solver is CaDiCaL 1.9.5.

Usage: satcensus2.py oracle.jsonl ns nm q out.jsonl [tables.jsonl|-] [planted]
Satisfiable instances are written with mu, nu (lists in itertools.product order), y, fwd, rev.
"""
import itertools, json, math, os, sys
from pysat.solvers import Solver


class Enc:
    def __init__(self, q):
        self.q, self.k, self.n, self.cl = q, max(1, math.ceil(math.log2(q))), 0, []

    def entry(self):
        bits = []
        for _ in range(self.k):
            self.n += 1
            bits.append(self.n)
        for code in range(self.q, 2 ** self.k):
            self.cl.append(self.neq(bits, code))
        return bits

    def neq(self, bits, a):
        return [-b if (a >> t) & 1 else b for t, b in enumerate(bits)]

    def eq_bits(self, bits, a):
        return [b if (a >> t) & 1 else -b for t, b in enumerate(bits)]

    def implies_eq(self, premises, bits, a):
        # premises: list of (bits, value) meaning AND of equalities; conclusion bits == a
        body = [lit for pb, pa in premises for lit in self.neq(pb, pa)]
        for lit in self.eq_bits(bits, a):
            self.cl.append(body + [lit])


def assignments(classes, q):
    for vals in itertools.product(range(q), repeat=len(classes)):
        yield {c: x for blk, x in zip(classes, vals) for c in blk}


def build(ns, nm, q, fwd, rev):
    S = ["1"] + [f"s{i}" for i in range(1, ns)]
    M = ["1"] + [f"m{i}" for i in range(1, nm)]
    e = Enc(q)
    mu = {t: e.entry() for t in itertools.product(range(q), repeat=nm)}
    nu = {t: e.entry() for t in itertools.product(range(q), repeat=ns)}
    for p in assignments(fwd, q):
        rows = [tuple(p[f"{s}|{m}"] for m in M) for s in S]
        for outs in itertools.product(range(q), repeat=ns):
            if any(rows[a] == rows[b] and outs[a] != outs[b] for a in range(ns) for b in range(a)):
                continue
            e.implies_eq([(mu[rows[a]], outs[a]) for a in range(ns)], nu[outs], p["1|1"])
    cls = {c: i for i, blk in enumerate(rev) for c in blk}
    y = [e.entry() for _ in rev]
    z = [e.entry() for _ in M]
    w = e.entry()
    for mi, m in enumerate(M):
        cells = [cls[f"{m}|{s}"] for s in S]
        for ins in itertools.product(range(q), repeat=ns):
            if any(cells[a] == cells[b] and ins[a] != ins[b] for a in range(ns) for b in range(a)):
                continue
            for val in range(q):
                e.implies_eq([(y[cells[a]], ins[a]) for a in range(ns)] + [(nu[ins], val)], z[mi], val)
    for ins in itertools.product(range(q), repeat=nm):
        for val in range(q):
            e.implies_eq([(z[a], ins[a]) for a in range(nm)] + [(mu[ins], val)], w, val)
    for val in range(q):
        e.cl.append(e.neq(w, val) + e.neq(y[cls["1|1"]], val))
    return e, mu, nu, y


def value(model, bits):
    pos = set(x for x in model if x > 0)
    return sum(1 << t for t, b in enumerate(bits) if b in pos)


def read_pairs(oracle_path, tables_path, ns, nm):
    S = ["1"] + [f"s{i}" for i in range(1, ns)]
    M = ["1"] + [f"m{i}" for i in range(1, nm)]
    orc = {}
    for line in open(oracle_path):
        r = json.loads(line)
        orc[r["id"]] = r
    keep = None
    if tables_path:
        keep = set()
        for line in open(tables_path):
            t = json.loads(line)
            word_cell = {}
            for s in S:
                for m in M:
                    word_cell.setdefault(tuple(t["fwd"][f"{s}|{m}"]), f"{s}|{m}")
            block = {c: frozenset([c]) for c in word_cell.values()}
            for a, b in t["rels"]:
                ca, cb = word_cell[tuple(a)], word_cell[tuple(b)]
                merged = block[ca] | block[cb]
                for c in merged:
                    block[c] = merged
            inp = frozenset(block.values())
            real = frozenset(frozenset(b) for b in orc[t["id"]]["fwd_classes"])
            if inp == real:
                keep.add(t["id"])
    seen = {}
    for tid, r in sorted(orc.items()):
        if not (r["resolved"] and r["labels_distinct"]) or (keep is not None and tid not in keep):
            continue
        key = (frozenset(frozenset(b) for b in r["fwd_classes"]), frozenset(frozenset(b) for b in r["rev_classes"]))
        seen.setdefault(key, []).append(tid)
    return seen


def main():
    orc, ns, nm, q, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    tables = sys.argv[6] if len(sys.argv) > 6 and sys.argv[6] != "-" else None
    planted = len(sys.argv) > 7 and sys.argv[7] == "planted"
    si, sk = map(int, os.environ.get("SHARD", "0/1").split("/"))
    M = ["1"] + [f"m{i}" for i in range(1, nm)]
    S = ["1"] + [f"s{i}" for i in range(1, ns)]
    pairs = sorted(read_pairs(orc, tables, ns, nm).items(), key=lambda kv: min(kv[1]))
    tot = {"encoding": "B", "q": q, "shape": f"{ns}x{nm}", "planted": planted, "shard": f"{si}/{sk}",
           "pairs": 0, "sat": 0, "unsat": 0}
    with open(out, "w") as fh:
        for n, ((fwd, rev), ids) in enumerate(pairs):
            if n % sk != si:
                continue
            tot["pairs"] += 1
            fwd = [sorted(b) for b in sorted(fwd, key=sorted)]
            rev = [[f"{m}|{s}"] for m in M for s in S] if planted else [sorted(b) for b in sorted(rev, key=sorted)]
            e, mu, nu, y = build(ns, nm, q, fwd, rev)
            with Solver(name="cd19", bootstrap_with=e.cl) as sol:
                sat = sol.solve()
                rec = {"ids": sorted(ids), "vars": e.n, "clauses": len(e.cl), "sat": sat}
                if sat:
                    mdl = sol.get_model()
                    rec.update(mu=[value(mdl, mu[t]) for t in itertools.product(range(q), repeat=nm)],
                               nu=[value(mdl, nu[t]) for t in itertools.product(range(q), repeat=ns)],
                               y=[value(mdl, b) for b in y], fwd=fwd, rev=rev)
            tot["sat" if sat else "unsat"] += 1
            fh.write(json.dumps(rec) + "\n")
    print(json.dumps(tot))


if __name__ == "__main__":
    main()
