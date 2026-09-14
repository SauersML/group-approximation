#!/usr/bin/env python3
"""Extended perturbation search for the open binary four-address survivor rules.

Builds on replay.py (same oracle, recognition, normal forms and merge rules), and adds:
  * flip sets F = {1} + W for W among longer words (single extra site) and pairs of short words
    (two extra sites), so perturbations flip up to three sites;
  * phased batching: all merge states of all candidate perturbations of one state are sent to GAP
    together;
  * a GAP-free collapse certificate: a merge u = v with u^-1 v equal in G_R to a memory quotient
    m_i^-1 m_j (i != j) forces m_i = m_j.
It also has a probe mode for the strongest candidates: the number of invisible perturbations with
up to four flipped sites inside the ball of radius 2 of the table group itself (finite collisions),
with no merge analysis.

Usage: search.py <flip1.json> <analyze3.json> <dflip3.json> <gap> <workdir> <mode> [rules...]
  mode = open  : search all survivors not closed by dflip3.json (or the listed rules)
  mode = probe : finite-collision probe on the listed rules' blocking partitions
"""
import itertools, json, os, sys
import replay as R


def build_instance(nf, flips):
    fk = [nf(f) for f in flips]
    if len(set(fk)) != len(fk):
        return None
    outs = {}
    for f in flips:
        for m in R.MEMW:
            o = R.wmul(f, R.winv(m))
            outs.setdefault(nf(o), o)
    rows, ctxw = [], {}
    for o in outs.values():
        row = []
        for m in R.MEMW:
            s = R.wmul(o, m)
            k = nf(s)
            if k in fk:
                row.append(("F", fk.index(k)))
            else:
                ctxw.setdefault(k, s)
                row.append(("C", k))
        rows.append(row)
    return {"flips": flips, "outs": list(outs.values()), "rows": rows, "ctxw": ctxw}


def merges(inst, sol):
    ctx = [(inst["ctxw"][k], b) for (kind, k), b in sol.items() if kind == "C"]
    rels = set()
    for (u, bu), (v, bv) in itertools.combinations(ctx, 2):
        if bu != bv:
            rels.add(R.wmul(R.winv(u), v))
    for u, _ in ctx:
        for f in inst["flips"]:
            rels.add(R.wmul(R.winv(u), f))
    for f1, f2 in itertools.combinations(inst["flips"], 2):
        rels.add(R.wmul(R.winv(f1), f2))
    for u, v in itertools.combinations(inst["outs"], 2):
        rels.add(R.wmul(R.winv(u), v))
    rels.discard(())
    return sorted(rels)


def flipsets(longest_single=3, pair_words=None):
    singles = [(w,) for w in R.words_upto(longest_single)]
    if pair_words is None:
        pair_words = R.words_upto(1) + [R.wmul(R.winv(R.MEMW[i]), R.MEMW[j]) for i, j in R.PAIRS]
        pair_words = list(dict.fromkeys(w for w in pair_words if w))
    pairs = list(itertools.combinations(pair_words, 2))
    return singles + pairs


class Search:
    def __init__(self, oracle, sets_root, sets_child, depth=1, sols_per_set=6, sol_limit=300):
        self.o, self.sets_root, self.sets_child = oracle, sets_root, sets_child
        self.depth, self.k, self.limit = depth, sols_per_set, sol_limit
        self.memo = {}

    def classify(self, key):
        res = R.recognize(self.o.get(key))
        if res.get("form") == "unrecognized":
            res2 = R.recognize(self.o.get(key, tryfinite=True))
            if res2.get("amenable"):
                return res2
        return res

    def closed_now(self, key):
        c = self.classify(key)
        if c.get("amenable") is True:
            return c["form"]
        if c.get("collapse"):
            return "memory-collapse(" + c["form"] + ")"
        return None

    def candidates(self, mu, key, nf, sets):
        memq = {nf(R.wmul(R.winv(R.MEMW[i]), R.MEMW[j])) for i, j in R.PAIRS}
        cands = []
        for fl in sets:
            inst = build_instance(nf, [()] + list(fl))
            if inst is None:
                continue
            sols = R.solutions(mu, inst, self.limit)
            scored = []
            for sol in sols:
                ms = merges(inst, sol)
                pending, cert = [], []
                for r in ms:
                    if nf(r) in memq:
                        cert.append({"merge": list(r), "closed": "memory-quotient-collapse"})
                    else:
                        pending.append(r)
                scored.append((len(pending), sol, pending, cert, inst))
            scored.sort(key=lambda t: t[0])
            cands.extend(scored[:self.k])
        cands.sort(key=lambda t: t[0])
        return cands

    def close(self, mu, key, depth):
        mk = (mu, key, depth)
        if mk in self.memo:
            return self.memo[mk]
        why = self.closed_now(key)
        if why:
            self.memo[mk] = {"closed": True, "why": why}
            return self.memo[mk]
        c = self.classify(key)
        if "nf" not in c:
            self.memo[mk] = {"closed": False, "why": "no-normal-form", "form": c.get("form")}
            return self.memo[mk]
        nf = c["nf"]
        cands = self.candidates(mu, key, nf, self.sets_root if depth == 0 else self.sets_child)
        ext = {}
        for n, sol, pending, cert, inst in cands[:3000]:
            for r in pending:
                ext.setdefault(r, R.state_key(list(key) + [r]))
        self.o.batch(list(ext.values()))
        unrec = [k for k in ext.values() if R.recognize(self.o.get(k)).get("form") == "unrecognized"]
        if unrec:
            self.o.batch(unrec, tryfinite=True)
        for n, sol, pending, cert, inst in cands[:3000]:
            certs, ok = list(cert), True
            open_children = []
            for r in pending:
                why = self.closed_now(ext[r])
                if why:
                    certs.append({"merge": list(r), "closed": why})
                else:
                    open_children.append(r)
            if open_children and (depth >= self.depth or len(open_children) > 2):
                continue
            for r in open_children:
                child = self.close(mu, ext[r], depth + 1)
                if not child["closed"]:
                    ok = False
                    break
                certs.append({"merge": list(r), "child": child})
            if ok:
                res = {"closed": True, "why": "perturbation", "flips": [list(f) for f in inst["flips"][1:]],
                       "assignment": {json.dumps([kind, list(inst["ctxw"][k]) if kind == "C" else list(inst["flips"][k])]): b
                                      for (kind, k), b in sol.items()},
                       "merges": certs}
                self.memo[mk] = res
                return res
        self.memo[mk] = {"closed": False, "why": "no-certificate", "form": c.get("form")}
        return self.memo[mk]


def audit_multi(mu, cert, quotients):
    stats = {"quotients": 0, "merge_holds": 0, "invisible": 0, "violations": 0}
    flips = [()] + [tuple(w) for w in cert["flips"]]
    assign = {}
    for k, b in cert["assignment"].items():
        kind, w = json.loads(k)
        assign[(kind, tuple(w))] = b
    merge_words = [tuple(m["merge"]) for m in cert["merges"]]
    for gens in quotients:
        gens = [tuple(g) for g in gens]
        stats["quotients"] += 1
        one = R.eval_perm((), gens)
        if any(R.eval_perm(r, gens) == one for r in merge_words):
            stats["merge_holds"] += 1
            continue
        x = {R.eval_perm(w, gens): b for (kind, w), b in assign.items()}
        x2 = dict(x)
        for f in flips:
            e = R.eval_perm(f, gens)
            x2[e] = 1 - x.get(e, 0)
        ok = True
        for f in flips:
            for m in R.MEMW:
                o = R.wmul(f, R.winv(m))
                b1 = [x.get(R.eval_perm(R.wmul(o, mm), gens), 0) for mm in R.MEMW]
                b2 = [x2.get(R.eval_perm(R.wmul(o, mm), gens), 0) for mm in R.MEMW]
                if R.rule_bit(mu, b1) != R.rule_bit(mu, b2):
                    ok = False
        stats["invisible" if ok else "violations"] += 1
    return stats


def collect(node, key, out):
    if node.get("closed") and node.get("why") == "perturbation":
        out.append((key, node))
        for m in node["merges"]:
            if "child" in m:
                collect(m["child"], R.state_key(list(key) + [tuple(m["merge"])]), out)


def probe(mu, key, oracle, maxflips=4, radius=2):
    c = R.recognize(oracle.get(key))
    if "nf" not in c:
        return {"form": c.get("form"), "probed": False}
    nf = c["nf"]
    ball = {}
    for w in [()] + R.words_upto(radius):
        ball.setdefault(nf(w), w)
    sites = [w for k, w in ball.items() if w]
    found = {}
    for size in range(1, maxflips):
        cnt = 0
        for extra in itertools.combinations(sites, size):
            inst = build_instance(nf, [()] + list(extra))
            if inst is None:
                continue
            if R.solutions(mu, inst, 1):
                cnt += 1
                if cnt == 1:
                    found[str(size + 1)] = [list(e) for e in extra]
        found["count_%d" % (size + 1)] = cnt
    return {"form": c.get("form"), "orders": c.get("orders"), "ball_sites": len(sites), "found": found}


def main():
    flip1, tri, dfl, gap, work, mode = sys.argv[1:7]
    only = sys.argv[7:]
    flip1, tri, dfl = json.load(open(flip1)), json.load(open(tri)), json.load(open(dfl))
    parts = flip1["partitions"]
    closed_prev = {str(x) for x in dfl["closed"]}
    oracle = R.Oracle(gap, work)
    rules = only or sorted((m for m in tri["survivors"] if m not in closed_prev), key=int)
    report = {"mode": mode, "rules": {}}
    if mode == "probe":
        for mu_s in rules:
            report["rules"][mu_s] = {k: probe(int(mu_s), R.partition_relators(parts[int(k)]), oracle)
                                     for k in tri["survivors"][mu_s]}
            sys.stderr.write("probe %s done\n" % mu_s)
            sys.stderr.flush()
        json.dump(report, sys.stdout)
        return
    sets_root = flipsets(int(os.environ.get("LONG", "3")))
    sets_child = [(w,) for w in R.words_upto(2)]
    s = Search(oracle, sets_root, sets_child, depth=int(os.environ.get("DEPTH", "1")))
    n_closed = 0
    for mu_s in rules:
        mu = int(mu_s)
        branches, allc = {}, True
        for k in tri["survivors"][mu_s]:
            res = s.close(mu, R.partition_relators(parts[int(k)]), 0)
            branches[k if isinstance(k, str) else str(k)] = res
            allc = allc and res["closed"]
        report["rules"][mu_s] = {"closed": allc, "branches": branches}
        n_closed += allc
        sys.stderr.write("rule %s closed=%s gapbatches=%d\n" % (mu_s, allc, oracle.calls))
        sys.stderr.flush()
    certs = []
    owner = {}
    for mu_s, rr in report["rules"].items():
        for k, node in rr["branches"].items():
            sub = []
            collect(node, R.partition_relators(parts[int(k)]), sub)
            for key, n2 in sub:
                owner[id(n2)] = int(mu_s)
            certs.extend(sub)
    keys = list(dict.fromkeys(key for key, _ in certs))
    quots = R.lowindex_quotients(gap, work, keys, int(os.environ.get("AUDIT_INDEX", "6"))) if keys else {}
    audit = {"certificates": len(certs), "states": len(keys), "quotients": 0, "merge_holds": 0,
             "invisible": 0, "violations": 0}
    for key, node in certs:
        st = audit_multi(owner[id(node)], node, quots.get(R.Oracle.skey(key), []))
        node["audit"] = st
        for f in ("quotients", "merge_holds", "invisible", "violations"):
            audit[f] += st[f]
    report["summary"] = {"rules": len(rules), "closed": n_closed, "open": len(rules) - n_closed,
                         "gap_batches": oracle.calls, "audit": audit}
    json.dump(report, sys.stdout, default=str)
    sys.stderr.write(json.dumps(report["summary"]) + "\n")


if __name__ == "__main__":
    main()
