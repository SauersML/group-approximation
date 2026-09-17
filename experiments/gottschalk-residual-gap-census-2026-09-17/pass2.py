#!/usr/bin/env python3
"""Second pass on CANDIDATE records of gapcensus.py: search harder for finite quotients.

For a candidate table T:
  1. rederive the reverse classes of P(T) with a longer Knuth-Bendix run (sound);
  2. try explicit finite quotients P(T)/<<extra relators>>, for the families
       (a) g^n = 1 for every generator g, n = 2..12;
       (b) g = 1 for a subset of generators, then family (a) on the rest;
     a quotient is used when Knuth-Bendix completes and the order is at most ORDMAX; its right regular
     representation is recorded as a permutation witness;
  3. run low-index subgroups (Sims1) up to degree NMAX with a time cap.
Witnesses satisfy the relators of P(T) (checked again by verify.py). A table stays CANDIDATE when some
pair of derived-distinct reverse classes is still unseparated.

Usage: pass2.py ns nm in.jsonl out.jsonl NMAX KBMS SIMSSEC
"""
import datetime
import itertools
import json
import sys
import time

from libsemigroups_pybind11 import KnuthBendix, Sims1, congruence_kind, presentation

from gapcensus import TableGroup, active_nodes, perm_of_word

ORDMAX = 5000


def regular_witness(G, extra, kbms):
    for (u, v) in extra:
        presentation.add_rule(G.p, u, v)
    kb = KnuthBendix(congruence_kind.twosided, G.p)
    kb.run_for(datetime.timedelta(milliseconds=kbms))
    if not kb.confluent():
        return None
    order = kb.number_of_classes()
    if not isinstance(order, int) or order > ORDMAX:
        return None
    nodes = {(): 0}
    queue = [()]
    for w in queue:
        for g in range(G.ng):
            v = tuple(kb.reduce_no_run(list(w) + [2 * g]))
            if v not in nodes:
                nodes[v] = len(nodes)
                queue.append(v)
    gens = [tuple(nodes[tuple(kb.reduce_no_run(list(w) + [2 * g]))] for w in queue) for g in range(G.ng)]
    return gens


def act(gens, w):
    pts = list(range(len(gens[0])))
    for a in w:
        pts = [gens[a // 2][x] for x in pts]
    return tuple(pts)


def main():
    ns, nm, fin, fout = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    NMAX, kbms, simssec = int(sys.argv[5]), int(sys.argv[6]), float(sys.argv[7])
    stats = {}
    with open(fout, "w") as fh:
        for line in open(fin):
            r = json.loads(line)
            if r["status"] != "CANDIDATE":
                continue
            key = r["table"]
            blocks = {}
            for c, v in enumerate(key):
                blocks.setdefault(v, []).append((c // nm, c % nm))
            part = [blocks[v] for v in sorted(blocks)]
            G = TableGroup(part, ns, nm)
            G.derive(kbms)
            cls = {c: bi for bi, b in enumerate(part) for c in b}
            fnf = {}
            for s in range(ns):
                for m in range(nm):
                    fnf.setdefault(G.nf(G.fw(s, m)), set()).add(cls[(s, m)])
            rec = {"id": r["id"], "table": key, "rels": G.rels, "confluent": G.confluent}
            if any(len(v) > 1 for v in fnf.values()):
                rec["status"] = "NOTCLOSED"
            else:
                rcells = [(m, s) for m in range(nm) for s in range(ns)]
                classes = {}
                for c in rcells:
                    classes.setdefault(G.nf(G.rv(*c)), []).append(c)
                reps = [v[0] for v in classes.values()]
                rec["rev_classes"] = sorted(classes.values())
                words = [G.rv(*c) for c in reps]
                pairs = set(itertools.combinations(range(len(reps)), 2))
                witnesses = []

                def use(gens, tag):
                    nonlocal pairs
                    perms = [act(gens, w) for w in words]
                    sep = {(i, j) for (i, j) in pairs if perms[i] != perms[j]}
                    if sep:
                        witnesses.append({"degree": len(gens[0]), "gens": gens, "separates": len(sep), "family": tag})
                        pairs -= sep

                gset = list(range(G.ng))
                for k in range(0, G.ng):
                    for kill in itertools.combinations(gset, k):
                        if not pairs:
                            break
                        for n in range(1, 13):
                            if not pairs:
                                break
                            if n == 1 and k > 0:
                                continue
                            extra = [([2 * g], []) for g in kill]
                            if n > 1:
                                extra += [([2 * g] * n, []) for g in gset if g not in kill]
                            gens = regular_witness(TableGroup(part, ns, nm), extra, 300)
                            if gens is not None:
                                use(gens, "kill%s-pow%d" % (list(kill), n))
                if pairs:
                    t0 = time.time()
                    for wg in Sims1(G.p).iterator(NMAX):
                        nn = active_nodes(wg, 2 * G.ng)
                        gens = [perm_of_word(wg, nn, [2 * g]) for g in range(G.ng)]
                        use(gens, "sims")
                        if not pairs or time.time() - t0 > simssec:
                            break
                rec["witnesses"] = witnesses
                if pairs:
                    rec["status"] = "CANDIDATE"
                    rec["unseparated"] = [[reps[i], reps[j]] for (i, j) in sorted(pairs)]
                else:
                    rec["status"] = "RESOLVED"
            stats[rec["status"]] = stats.get(rec["status"], 0) + 1
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            print(r["id"], rec["status"], len(rec.get("unseparated", [])), flush=True)
    print("pass2", stats, flush=True)


if __name__ == "__main__":
    main()
