#!/usr/bin/env python3
"""Rule-free residual-gap census of forward-table groups (all alphabets at once).

Setting: surjunctivity-is-axiomatized-by-rectangle-clauses and
strict-automata-live-on-canonical-table-groups. Labels S = {1, s1, ...}, M = {1, m1, ...}.
A forward table T is a rook-independent partition of S x M. Its table group is

    P(T) = < x_a (a != 1) | x_s x_m = x_s' x_m'  along T >.

Resolution lemma (proved in the artifact): if some finite quotient Q of P(T) has
the same reverse table as P(T) on the cells x_m x_s (m in M, s in S), then no
strict rule pair over ANY alphabet uses forward table T. So a table can host a
counterexample only if it is a *gap table*: some pair of reverse cells is
distinct in P(T) but merged in every finite quotient.

Per table this script
  1. derives equalities among forward and reverse cell words (Knuth-Bendix with a
     time cap; every reported equality is a consequence of the relators, so it is
     sound even when completion does not finish);
  2. discards tables whose group derives a forward coincidence outside T
     (not closed: covered by the coarser table);
  3. for each pair of derived-distinct reverse classes, looks for a transitive
     permutation representation of degree <= NMAX (low-index subgroups, Sims1)
     separating the two words as permutations;
  4. classifies the table as RESOLVED (every pair separated; then the derived
     table is exact and is realized by a finite group) or CANDIDATE (some pair
     unseparated), recording the unseparated pairs.

Usage: gapcensus.py ns nm NMAX KBMS out.jsonl [start stop]
"""
import datetime
import itertools
import json
import sys
import time

from libsemigroups_pybind11 import (KnuthBendix, Presentation, ReportGuard,
                                    Sims1, congruence_kind, presentation)

RG = ReportGuard(False)


def rook_partitions(ns, nm):
    cells = [(s, m) for s in range(ns) for m in range(nm)]
    blocks = []

    def rec(i):
        if i == len(cells):
            yield [list(b[2]) for b in blocks]
            return
        s, m = cells[i]
        for b in blocks:
            if s not in b[0] and m not in b[1]:
                b[0].add(s); b[1].add(m); b[2].append((s, m))
                yield from rec(i + 1)
                b[0].discard(s); b[1].discard(m); b[2].pop()
        blocks.append(({s}, {m}, [(s, m)]))
        yield from rec(i + 1)
        blocks.pop()

    yield from rec(0)


def canon_key(part, ns, nm):
    """Canonical form under Sym(S minus 1) x Sym(M minus 1)."""
    best = None
    for ps in itertools.permutations(range(1, ns)):
        sp = (0,) + ps
        for pm in itertools.permutations(range(1, nm)):
            mp = (0,) + pm
            lab = {}
            for bi, b in enumerate(part):
                for (s, m) in b:
                    lab[(sp[s], mp[m])] = bi
            ren = {}
            seq = []
            for s in range(ns):
                for m in range(nm):
                    c = lab[(s, m)]
                    if c not in ren:
                        ren[c] = len(ren)
                    seq.append(ren[c])
            t = tuple(seq)
            if best is None or t < best:
                best = t
    return best


class TableGroup:
    def __init__(self, part, ns, nm):
        self.ns, self.nm = ns, nm
        # generator index: s_i (i=1..ns-1) -> i-1 ; m_j -> ns-1 + j-1 ; letters 2*g, inverse 2*g+1
        self.ng = ns - 1 + nm - 1
        self.part = part
        p = Presentation(list(range(2 * self.ng)))
        p.contains_empty_word(True)
        inv = []
        for g in range(self.ng):
            inv += [2 * g + 1, 2 * g]
        presentation.add_inverse_rules(p, inv)
        self.rels = []
        for b in part:
            w0 = self.fw(*b[0])
            for c in b[1:]:
                w1 = self.fw(*c)
                if w0 != w1:
                    presentation.add_rule(p, w0, w1)
                    self.rels.append((w0, w1))
        self.p = p

    def ls(self, s):
        return [] if s == 0 else [2 * (s - 1)]

    def lm(self, m):
        return [] if m == 0 else [2 * (self.ns - 1 + m - 1)]

    def fw(self, s, m):
        return self.ls(s) + self.lm(m)

    def rv(self, m, s):
        return self.lm(m) + self.ls(s)

    def derive(self, ms):
        kb = KnuthBendix(congruence_kind.twosided, self.p)
        kb.run_for(datetime.timedelta(milliseconds=ms))
        self.confluent = bool(kb.confluent())
        self.kb = kb
        return kb

    def nf(self, w):
        return tuple(self.kb.reduce_no_run(w))


def active_nodes(wg, nletters):
    seen = {0}
    stack = [0]
    while stack:
        x = stack.pop()
        for a in range(nletters):
            y = wg.target(x, a)
            if isinstance(y, int) and y not in seen:
                seen.add(y)
                stack.append(y)
    assert seen == set(range(len(seen)))
    return len(seen)


def perm_of_word(wg, n, w):
    pts = list(range(n))
    for a in w:
        pts = [wg.target(x, a) for x in pts]
    return tuple(pts)


def analyse(part, ns, nm, NMAX, kbms):
    G = TableGroup(part, ns, nm)
    G.derive(kbms)
    rec = {"rels": G.rels, "confluent": G.confluent}
    order = None
    if G.confluent:
        order = G.kb.number_of_classes()
        rec["order"] = order if isinstance(order, int) else "inf"
    # forward closedness
    cls = {}
    for bi, b in enumerate(part):
        for c in b:
            cls[c] = bi
    fnf = {}
    for s in range(ns):
        for m in range(nm):
            fnf[(s, m)] = G.nf(G.fw(s, m))
    merged = {}
    for c, v in fnf.items():
        merged.setdefault(v, set()).add(cls[c])
    if any(len(v) > 1 for v in merged.values()):
        rec["status"] = "NOTCLOSED"
        return rec
    # reverse derived classes
    rcells = [(m, s) for m in range(nm) for s in range(ns)]
    rnf = {c: G.nf(G.rv(*c)) for c in rcells}
    classes = {}
    for c in rcells:
        classes.setdefault(rnf[c], []).append(c)
    reps = [v[0] for v in classes.values()]
    rec["rev_classes"] = sorted(classes.values())
    pairs = set(itertools.combinations(range(len(reps)), 2))
    words = [G.rv(*c) for c in reps]
    sims = Sims1(G.p)
    witnesses = []
    if pairs and isinstance(order, int) and order <= 20000:
        # P(T) is finite with exact (confluent) word problem: its right regular
        # representation, built from normal forms, is a finite quotient realizing its own table.
        rec["finite_self"] = True
        nodes = {(): 0}
        queue = [()]
        for w in queue:
            for g in range(G.ng):
                v = G.nf(list(w) + [2 * g])
                if v not in nodes:
                    nodes[v] = len(nodes)
                    queue.append(v)
        assert len(nodes) == order
        gens = [tuple(nodes[G.nf(list(w) + [2 * g])] for w in queue) for g in range(G.ng)]
        witnesses.append({"degree": order, "gens": gens, "separates": len(pairs), "regular": True})
        pairs = set()
    if pairs:
        for wg in sims.iterator(NMAX):
            nn = active_nodes(wg, 2 * G.ng)
            perms = [perm_of_word(wg, nn, w) for w in words]
            sep = {(i, j) for (i, j) in pairs if perms[i] != perms[j]}
            if sep:
                gens = [perm_of_word(wg, nn, [2 * g]) for g in range(G.ng)]
                witnesses.append({"degree": nn, "gens": gens, "separates": len(sep)})
                pairs -= sep
                if not pairs:
                    break
    rec["witnesses"] = witnesses
    if pairs:
        rec["status"] = "CANDIDATE"
        rec["unseparated"] = [[reps[i], reps[j]] for (i, j) in sorted(pairs)]
    else:
        rec["status"] = "RESOLVED"
    return rec


def main_reps():
    # gapcensus.py reps ns nm repsfile NMAX KBMS out.jsonl [start stop]
    ns, nm, repsfile = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    NMAX, kbms, out = int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
    start = int(sys.argv[8]) if len(sys.argv) > 8 else 0
    stop = int(sys.argv[9]) if len(sys.argv) > 9 else 10 ** 12
    stats = {}
    t0 = time.time()
    with open(repsfile) as fin, open(out, "w") as fh:
        for idx, line in enumerate(fin):
            if idx < start or idx >= stop:
                continue
            key = tuple(int(v) for v in line.split())
            blocks = {}
            for c, v in enumerate(key):
                blocks.setdefault(v, []).append((c // nm, c % nm))
            part = [blocks[v] for v in sorted(blocks)]
            rec = analyse(part, ns, nm, NMAX, kbms)
            rec["id"] = idx
            rec["table"] = key
            stats[rec["status"]] = stats.get(rec["status"], 0) + 1
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
    print(ns, nm, "reps", start, stop, stats, "time %.1f" % (time.time() - t0), flush=True)


def main():
    if sys.argv[1] == "reps":
        return main_reps()
    ns, nm, NMAX, kbms, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    start = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    stop = int(sys.argv[7]) if len(sys.argv) > 7 else 10 ** 12
    seen = set()
    stats = {}
    t0 = time.time()
    idx = -1
    with open(out, "w") as fh:
        for part in rook_partitions(ns, nm):
            key = canon_key(part, ns, nm)
            if key in seen:
                continue
            seen.add(key)
            idx += 1
            if idx < start or idx >= stop:
                continue
            rec = analyse(part, ns, nm, NMAX, kbms)
            rec["id"] = idx
            rec["table"] = key
            stats[rec["status"]] = stats.get(rec["status"], 0) + 1
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
    print(ns, nm, "orbits", idx + 1, stats, "time %.1f" % (time.time() - t0), flush=True)


if __name__ == "__main__":
    main()
