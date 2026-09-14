#!/usr/bin/env python3
"""Enumerate forward tables for rectangle data with |S| = ns, |M| = nm (labels include 1).

A forward cell (s, m) stands for the product x_s x_m. A forward table is a set
partition of the cells in which no block contains two cells of one row or one
column. (Cells in one row differ because the labels x_m are distinct elements;
likewise for columns.) For every table we emit the finitely presented group
P(T_f) = < x_a (a != 1) | x_s x_m = x_s' x_m' along blocks >, together with the
forward words (s, m) -> x_s x_m and the reverse words (m, s) -> x_m x_s, and the
labels, so an oracle can compute the realized forward and reverse tables.

Output: JSON lines, one per table:
  {"id", "ns", "nm", "gens", "rels": [[word, word], ...],
   "fwd": {cell: word}, "rev": {cell: word}, "labels": {label: word}}
A word is a list of generator names; the empty list is the identity.
"""
import itertools, json, sys

def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for part in set_partitions(rest):
        for i in range(len(part)):
            yield part[:i] + [[first] + part[i]] + part[i + 1:]
        yield [[first]] + part

def independent(block):
    rows = [c[0] for c in block]
    cols = [c[1] for c in block]
    return len(set(rows)) == len(rows) and len(set(cols)) == len(cols)

def main(ns, nm, out):
    S = ["1"] + [f"s{i}" for i in range(1, ns)]
    M = ["1"] + [f"m{i}" for i in range(1, nm)]
    gens = S[1:] + M[1:]
    cells = [(s, m) for s in S for m in M]

    def w(*labels):
        return [a for a in labels if a != "1"]

    n = 0
    with open(out, "w") as fh:
        for part in set_partitions(cells):
            if not all(independent(b) for b in part):
                continue
            rels = []
            for b in part:
                for c in b[1:]:
                    rels.append([w(b[0][0], b[0][1]), w(c[0], c[1])])
            rec = {
                "id": n, "ns": ns, "nm": nm, "gens": gens, "rels": rels,
                "fwd": {f"{s}|{m}": w(s, m) for (s, m) in cells},
                "rev": {f"{m}|{s}": w(m, s) for (s, m) in cells},
                "labels": {a: w(a) for a in S + M},
            }
            fh.write(json.dumps(rec) + "\n")
            n += 1
    print(f"ns={ns} nm={nm}: {n} tables -> {out}")

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3])
