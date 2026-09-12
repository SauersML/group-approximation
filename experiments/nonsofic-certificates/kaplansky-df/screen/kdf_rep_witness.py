#!/usr/bin/env python3
"""Test the nine-leaf GL(6,2) block representation as a realization of a df table group U(A, B).

Uses the representation of experiments/gottschalk-small-presentations/nine_leaf_corner_rep.py
(E_ij(r) -> 1 + e_ij (x) rho_ij(r), compressors -> 1). Its witness there was checked against a
different table (invariant-output windows), so here every relator of U(A, B) is replayed.
The script writes <tag>--rep.witness.jsonl for df_table_screen.py --verify and prints how many
relators fail and how far the image alone refines BA u {1}.

usage: python kdf_rep_witness.py <family> <ra> <rb> <gap_dir>
"""
import json
import os
import re
import sys

sys.path.insert(0, "/projects/standard/hsiehph/sauer354/kdf-screen/screen")
import df_table_screen as T  # noqa: E402

NPTS = 63
RHO = {(0, 1): {"1": [(0, 0)]},
       (0, 2): {"1": [(0, 0)], "t0": [(0, 0)], "t1": [(0, 1)]},
       (2, 1): {"1": [(0, 0)], "s0": [(0, 0)], "s1": [(1, 0)]}}
RHO[(1, 2)] = RHO[(0, 2)]
RHO[(2, 0)] = RHO[(2, 1)]


def base_perm(name):
    rows = [1 << k for k in range(6)]
    m = re.match(r"E(\d)(\d)_(\w+)$", name)
    if m:
        i, j, r = int(m.group(1)), int(m.group(2)), m.group(3)
        for a, b in RHO.get((i, j), {}).get(r, []):
            rows[2 * i + a] ^= 1 << (2 * j + b)

    def act(v):
        out = 0
        for k in range(6):
            if (v >> k) & 1:
                out ^= rows[k]
        return out
    return [act(p) for p in range(1, NPTS + 1)]


def invert(perm):
    inv = [0] * len(perm)
    for i, x in enumerate(perm):
        inv[x - 1] = i + 1
    return inv


def main():
    fam, ra, rb, gdir = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    tag = "%s-%d-%d" % (fam, ra, rb)
    nA, nB, cells, rels, ba = T.table(fam, ra, rb)
    basic, word, crels = T.compact(cells, rels)
    name_of = {}
    for n, g in T.family_gens(fam).items():
        name_of.setdefault(g.key, (n, 1))
        name_of.setdefault(g.inverse().key, (n, -1))
    perms, unnamed = [], 0
    for k in basic:
        if cells[k].key not in name_of:
            unnamed += 1
            perms.append(list(range(1, NPTS + 1)))
            continue
        n, e = name_of[cells[k].key]
        p = base_perm(n)
        perms.append(p if e == 1 else invert(p))
    if unnamed:
        print(tag, "basic cells that are not generators:", unnamed, "(sent to 1; relator replay decides)")
    os.makedirs(gdir, exist_ok=True)
    wpath = os.path.join(gdir, tag + "--rep.witness.jsonl")
    with open(wpath, "w") as fh:
        fh.write(json.dumps({"tag": "nine-leaf GL(6,2) rep", "degree": NPTS, "perms": perms}) + "\n")
    keys, used, bad = T.replay_images(cells, rels, ba, word, [wpath], {g: () for g in ba})
    cl = T.classes(keys)
    merged = sum(len(c) for c in cl)
    print(tag, "relators", len(rels), "rep used", used, "rejected", bad,
          "classes", len(cl), "merged", merged, "singletons", len(ba) - merged,
          "largest", max((len(c) for c in cl), default=0))
    if bad:
        os.remove(wpath)
        print(tag, "rep is not a realization of this table; witness removed")
    print("REP_DONE", tag)


if __name__ == "__main__":
    main()
