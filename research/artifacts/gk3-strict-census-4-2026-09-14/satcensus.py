#!/usr/bin/env python3
"""SAT census of strict rectangle data at realized (forward, reverse) tables.

Data: label sets S = {1, s1, ...} (ns labels) and M = {1, m1, ...} (nm labels), an alphabet
of size q, a forward partition T_f of the cells "s|m" and a reverse partition T_r of the
cells "m|s". The CNF built here is satisfiable iff rules mu: A^M -> A and nu: A^S -> A exist with
  Dec(T_f):     nu((mu(p(s, .)))_s) = p(1,1)   for every p constant on T_f classes, and
  not Enc(T_r): mu((nu(y(m, .)))_m) != y(1,1)  for some y constant on T_r classes
(`surjunctivity-is-axiomatized-by-rectangle-clauses`). Encoding A: one-hot symbols.
Tables are indexed big-endian in label order (1, m1, m2, ...) and (1, s1, s2, ...).

Modes
  strict   : decide Dec and not Enc at the realized reverse table. UNSAT instances get a DRUP
             proof from glucose4, checked by drat-trim when a proof dir is given.
  countdec : count the rules mu for which some nu satisfies Dec (projected enumeration).
  planted  : strict, but at the discrete reverse table (calibrates the satisfiable side).

Usage: satcensus.py MODE oracle.jsonl ns nm q out.jsonl [tables.jsonl|-] [proofdir drat-trim]
With tables.jsonl only closed tables (realized forward partition = input partition) are used.
Realized (forward, reverse) pairs are deduplicated and every source table id is recorded.
"""
import gzip, hashlib, itertools, json, os, subprocess, sys
from pysat.solvers import Solver


def labels(ns, nm):
    return ["1"] + [f"s{i}" for i in range(1, ns)], ["1"] + [f"m{i}" for i in range(1, nm)]


class CNF:
    def __init__(self):
        self.n, self.cl = 0, []

    def var(self):
        self.n += 1
        return self.n

    def add(self, c):
        c = sorted(set(c), key=lambda x: (abs(x), x))
        if any(-x in c for x in c):
            return
        self.cl.append(c)


def one_hot(cnf, vs, exact):
    if exact:
        cnf.add(list(vs))
    for a, b in itertools.combinations(vs, 2):
        cnf.add([-a, -b])


def index(tup, q):
    j = 0
    for x in tup:
        j = j * q + x
    return j


def consistent(cells, b):
    return all(not (cells[k] == cells[l] and b[k] != b[l]) for k in range(len(b)) for l in range(k))


def build(ns, nm, q, fwd, rev, with_enc=True):
    S, M = labels(ns, nm)
    fc = {c: i for i, blk in enumerate(fwd) for c in blk}
    cnf = CNF()
    u = [[cnf.var() for _ in range(q)] for _ in range(q ** nm)]
    v = [[cnf.var() for _ in range(q)] for _ in range(q ** ns)]
    for row in u + v:
        one_hot(cnf, row, True)
    keys = set()
    for p in itertools.product(range(q), repeat=len(fwd)):
        r = tuple(index([p[fc[f"{s}|{m}"]] for m in M], q) for s in S)
        keys.add((r, p[fc["1|1"]]))
    for r, d in sorted(keys):
        for b in itertools.product(range(q), repeat=ns):
            if consistent(r, b):
                cnf.add([-u[r[k]][b[k]] for k in range(ns)] + [v[index(b, q)][d]])
    y = None
    if with_enc:
        rc = {c: i for i, blk in enumerate(rev) for c in blk}
        y = [[cnf.var() for _ in range(q)] for _ in range(len(rev))]
        for row in y:
            one_hot(cnf, row, True)
        z = [[cnf.var() for _ in range(q)] for _ in M]
        for row in z:
            one_hot(cnf, row, False)
        for mi, m in enumerate(M):
            cells = [rc[f"{m}|{s}"] for s in S]
            for b in itertools.product(range(q), repeat=ns):
                if consistent(cells, b):
                    for a in range(q):
                        cnf.add([-y[cells[k]][b[k]] for k in range(ns)] + [-v[index(b, q)][a], z[mi][a]])
        w = [cnf.var() for _ in range(q)]
        one_hot(cnf, w, False)
        for c in itertools.product(range(q), repeat=nm):
            for a in range(q):
                cnf.add([-z[k][c[k]] for k in range(nm)] + [-u[index(c, q)][a], w[a]])
        for a in range(q):
            cnf.add([-w[a], -y[rc["1|1"]][a]])
    return cnf, u, v, y


def decode(model, table):
    pos = {x for x in model if x > 0}
    return [next(a for a, x in enumerate(row) if x in pos) for row in table]


def canon(classes):
    return tuple(sorted(tuple(sorted(b)) for b in classes))


def input_partition(t, S, M):
    cells = [f"{s}|{m}" for s in S for m in M]
    cell_of = {}
    for c in cells:
        cell_of.setdefault(tuple(t["fwd"][c]), c)
    parent = {c: c for c in cells}

    def find(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c
    for a, b in t["rels"]:
        parent[find(cell_of[tuple(a)])] = find(cell_of[tuple(b)])
    blocks = {}
    for c in cells:
        blocks.setdefault(find(c), []).append(c)
    return canon(blocks.values())


def realized_pairs(oracle_path, tables_path, ns, nm):
    S, M = labels(ns, nm)
    recs = {r["id"]: r for r in map(json.loads, open(oracle_path))}
    use = [o for o in recs.values() if o["resolved"] and o["labels_distinct"]]
    if tables_path:
        closed = {t["id"] for t in map(json.loads, open(tables_path))
                  if t["id"] in recs and input_partition(t, S, M) == canon(recs[t["id"]]["fwd_classes"])}
        use = [o for o in use if o["id"] in closed]
    groups = {}
    for o in use:
        groups.setdefault((canon(o["fwd_classes"]), canon(o["rev_classes"])), []).append(o["id"])
    return sorted(groups.items())


def md5(path):
    return hashlib.md5(open(path, "rb").read()).hexdigest()


def main():
    mode, orc, ns, nm, q, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    tables = sys.argv[7] if len(sys.argv) > 7 and sys.argv[7] != "-" else None
    proofdir = sys.argv[8] if len(sys.argv) > 8 else None
    drat = sys.argv[9] if len(sys.argv) > 9 else None
    S, M = labels(ns, nm)
    tot = {"mode": mode, "q": q, "shape": f"{ns}x{nm}", "pairs": 0, "sat": 0, "unsat": 0,
           "drat_verified": 0, "drat_failed": 0, "mus_with_dec": 0}
    si, sk = map(int, os.environ.get("SHARD", "0/1").split("/"))
    tot["shard"] = f"{si}/{sk}"
    with open(out, "w") as fh:
        for n, ((fwd, rev), ids) in enumerate(realized_pairs(orc, tables, ns, nm)):
            if n % sk != si:
                continue
            tot["pairs"] += 1
            fwd = [list(b) for b in fwd]
            rev = [list(b) for b in rev]
            if mode == "planted":
                rev = [[f"{m}|{s}"] for m in M for s in S]
            if mode == "countdec":
                cnf, u, _, _ = build(ns, nm, q, fwd, rev, with_enc=False)
                k = 0
                with Solver(name="cd19", bootstrap_with=cnf.cl) as sol:
                    while sol.solve():
                        mu = decode(sol.get_model(), u)
                        k += 1
                        sol.add_clause([-u[i][a] for i, a in enumerate(mu)])
                tot["mus_with_dec"] += k
                fh.write(json.dumps({"pair": n, "ids": ids, "mus_with_dec": k}) + "\n")
                continue
            cnf, u, v, y = build(ns, nm, q, fwd, rev)
            sol = Solver(name="g4", bootstrap_with=cnf.cl, with_proof=bool(proofdir))
            sat = sol.solve()
            rec = {"pair": n, "ids": ids, "vars": cnf.n, "clauses": len(cnf.cl), "sat": sat}
            if sat:
                tot["sat"] += 1
                mdl = sol.get_model()
                rec.update(mu=decode(mdl, u), nu=decode(mdl, v), y=decode(mdl, y), fwd=fwd, rev=rev)
            else:
                tot["unsat"] += 1
                if proofdir:
                    base = os.path.join(proofdir, f"{mode}_q{q}_{ns}x{nm}_{n}")
                    with open(base + ".cnf", "w") as cf:
                        cf.write(f"p cnf {cnf.n} {len(cnf.cl)}\n")
                        cf.writelines(" ".join(map(str, c)) + " 0\n" for c in cnf.cl)
                    with open(base + ".drup", "w") as pf:
                        pf.writelines(line + "\n" for line in sol.get_proof())
                    rec.update(cnf_md5=md5(base + ".cnf"), proof_md5=md5(base + ".drup"))
                    if drat:
                        res = subprocess.run([drat, base + ".cnf", base + ".drup", "-t",
                                              os.environ.get("DRAT_TIMEOUT", "20000")],
                                             capture_output=True, text=True)
                        ok = "s VERIFIED" in res.stdout
                        rec["drat"] = "VERIFIED" if ok else res.stdout[-300:]
                        tot["drat_verified" if ok else "drat_failed"] += 1
                    for ext in (".cnf", ".drup"):
                        with open(base + ext, "rb") as src, gzip.open(base + ext + ".gz", "wb") as dst:
                            dst.write(src.read())
                        os.remove(base + ext)
            sol.delete()
            fh.write(json.dumps(rec) + "\n")
    print(json.dumps(tot))


if __name__ == "__main__":
    main()
