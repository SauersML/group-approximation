#!/usr/bin/env python3
"""Second stage for forward tables that survive enum4.py.

For each table T (enum_tables format), in order:
 1. Sofic exclusion. tietze2.decide(T); if P(T) is cyclic, free, or free abelian of rank two, it is
    sofic, hence surjunctive, so no strict data with realized forward table T exist in any group
    (the reduction of the binary census: such data are realized in P(T)).
 2. Degenerate labels. After Tietze elimination, substitute the label words and reduce freely.
    Equal reduced words are equal in P(T); two equal labels in S (or in M) mean T is only realized
    on a smaller memory, which is a smaller shape.
 3. Lower bound. Reverse cells whose substituted reduced words agree are equal in P(T), so that
    partition T_lb is finer than or equal to the realized reverse table. Not-Enc passes to finer
    tables, so if Dec(T) and not Enc(T_lb) is UNSAT over an alphabet of size q, T carries no strict
    data at that alphabet. The DRUP proof of glucose4 is checked by drat-trim.
 4. Tables whose instance at T_lb is satisfiable go to the exact word-problem stage (oracle.py,
    certify.py, then satcensus.py at the realized tables).

Usage: SHARD=i/k stage2.py survivors.jsonl ns nm q out.jsonl escalate.jsonl proofdir drat-trim
"""
import gzip, hashlib, json, os, subprocess, sys
from pysat.solvers import Solver
import satcensus as SC
import tietze as T
import tietze2 as T2


def md5(path):
    return hashlib.md5(open(path, "rb").read()).hexdigest()


def solve_with_proof(ns, nm, q, fwd, rev, base, drat):
    cnf, u, v, y = SC.build(ns, nm, q, fwd, rev)
    sol = Solver(name="g4", bootstrap_with=cnf.cl, with_proof=True)
    sat = sol.solve()
    rec = {"vars": cnf.n, "clauses": len(cnf.cl), "sat": sat}
    if sat:
        mdl = sol.get_model()
        rec.update(mu=SC.decode(mdl, u), nu=SC.decode(mdl, v), y=SC.decode(mdl, y))
    else:
        with open(base + ".cnf", "w") as cf:
            cf.write(f"p cnf {cnf.n} {len(cnf.cl)}\n")
            cf.writelines(" ".join(map(str, c)) + " 0\n" for c in cnf.cl)
        with open(base + ".drup", "w") as pf:
            pf.writelines(line + "\n" for line in sol.get_proof())
        res = subprocess.run([drat, base + ".cnf", base + ".drup", "-t", os.environ.get("DRAT_TIMEOUT", "20000")],
                             capture_output=True, text=True)
        rec["drat"] = "VERIFIED" if "s VERIFIED" in res.stdout else res.stdout[-300:]
        rec["cnf_md5"], rec["proof_md5"] = md5(base + ".cnf"), md5(base + ".drup")
        for ext in (".cnf", ".drup"):
            with open(base + ext, "rb") as src, gzip.open(base + ext + ".gz", "wb") as dst:
                dst.write(src.read())
            os.remove(base + ext)
    sol.delete()
    return rec


def main():
    surv, ns, nm, q, out, esc, proofdir, drat = (sys.argv[1], int(sys.argv[2]), int(sys.argv[3]),
                                                  int(sys.argv[4]), sys.argv[5], sys.argv[6], sys.argv[7], sys.argv[8])
    si, sk = map(int, os.environ.get("SHARD", "0/1").split("/"))
    S, M = SC.labels(ns, nm)
    os.makedirs(proofdir, exist_ok=True)
    st = {"shape": f"{ns}x{nm}", "q": q, "shard": f"{si}/{sk}", "tables": 0, "mass": 0,
          "sofic": {}, "degenerate": 0, "unsat_lb": 0, "drat_verified": 0, "drat_failed": 0,
          "escalate": 0, "escalate_mass": 0}
    with open(out, "w") as fh, open(esc, "w") as fe:
        for n, line in enumerate(open(surv)):
            if n % sk != si:
                continue
            t = json.loads(line)
            st["tables"] += 1
            st["mass"] += t.get("orbit", 1)
            rec = {"id": t["id"], "orbit": t.get("orbit", 1)}
            d = T2.decide(t)
            if d["kind"] != "undecided":
                st["sofic"][d["kind"]] = st["sofic"].get(d["kind"], 0) + 1
                rec["excluded"] = "sofic-" + d["kind"]
                fh.write(json.dumps(rec) + "\n")
                continue
            rem, rels, sub, order = T.tietze(t["gens"], t["rels"])
            key = lambda w: tuple(T.subst(list(w), sub))
            if len({key(t["labels"][a]) for a in S}) < ns or len({key(t["labels"][a]) for a in M}) < nm:
                st["degenerate"] += 1
                rec["excluded"] = "degenerate-labels"
                fh.write(json.dumps(rec) + "\n")
                continue
            groups = {}
            for c, w in t["rev"].items():
                groups.setdefault(key(w), []).append(c)
            rev = [sorted(b) for b in groups.values()]
            fwd = [list(b) for b in SC.input_partition(t, S, M)]
            r = solve_with_proof(ns, nm, q, fwd, rev, os.path.join(proofdir, f"lb_q{q}_{ns}x{nm}_{t['id']}"), drat)
            rec.update(r, remaining=rem, relators=len(rels), rev_lb_classes=len(rev))
            if not r["sat"]:
                st["unsat_lb"] += 1
                st["drat_verified" if r.get("drat") == "VERIFIED" else "drat_failed"] += 1
                rec["excluded"] = "unsat-at-lower-bound"
            else:
                st["escalate"] += 1
                st["escalate_mass"] += t.get("orbit", 1)
                fe.write(json.dumps(t) + "\n")
            fh.write(json.dumps(rec) + "\n")
    print(json.dumps(st))


if __name__ == "__main__":
    main()
