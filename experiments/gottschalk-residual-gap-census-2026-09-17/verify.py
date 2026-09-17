#!/usr/bin/env python3
"""Independent certificate check for RESOLVED records of gapcensus.py (pure Python, no libsemigroups).

For each RESOLVED record:
  * every witness (a tuple of permutations, one per generator x_a, a != 1, acting on the right)
    satisfies every relator x_s x_m = x_s' x_m' of the table group, so it is a finite quotient of P(T);
  * in the product of the witnesses, the partition of the reverse cells x_m x_s by their permutations
    equals the recorded reverse classes (the classes were derived by Knuth-Bendix, i.e. by genuine
    consequences of the relators; this check confirms that every distinct pair is separated by a finite
    quotient, so the recorded classes are exactly the reverse table of P(T)).
Later records with the same id supersede earlier ones only in the sense that each RESOLVED record is checked on its own.
Usage: verify.py ns nm file.jsonl[.gz] [more ...]
"""
import gzip
import json
import sys


def act(gens, w):
    n = len(gens[0])
    pts = list(range(n))
    for a in w:
        pts = [gens[a // 2][x] for x in pts]  # only positive letters occur in relators and cell words
    return tuple(pts)


def main():
    ns, nm = int(sys.argv[1]), int(sys.argv[2])
    ok = bad = 0
    for f in sys.argv[3:]:
        for line in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f)):
            r = json.loads(line)
            if r["status"] != "RESOLVED":
                continue

            def ls(s):
                return [] if s == 0 else [2 * (s - 1)]

            def lm(m):
                return [] if m == 0 else [2 * (ns - 1 + m - 1)]
            wits = r["witnesses"]
            good = True
            for wt in wits:
                g = wt["gens"]
                for p in g:
                    if sorted(p) != list(range(len(p))):
                        good = False
                for (u, v) in r["rels"]:
                    if act(g, u) != act(g, v):
                        good = False
            rcells = [(m, s) for m in range(nm) for s in range(ns)]
            sig = {c: tuple(act(wt["gens"], lm(c[0]) + ls(c[1])) for wt in wits) for c in rcells}
            part = {}
            for c in rcells:
                part.setdefault(sig[c], []).append(list(c))
            if sorted(sorted(v) for v in part.values()) != sorted(sorted(v) for v in r["rev_classes"]):
                good = False
            if good:
                ok += 1
            else:
                bad += 1
                print("FAIL", f, r["id"])
    print("verified", ok, "failed", bad)


if __name__ == "__main__":
    main()
