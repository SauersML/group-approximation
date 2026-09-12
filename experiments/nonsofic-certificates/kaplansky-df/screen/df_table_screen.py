#!/usr/bin/env python3
"""Rule-free screen of support windows for one-sided inverse pairs in F_2[R^x], R = L_{F_2}(1,2).

research/one-sided-inverse-pairs-transfer-to-table-realizations.md, Corollary 1. Suppose
alpha beta = 1 != beta alpha, with supp alpha in A and supp beta in B. Then every realization
phi of the product tables A x B and B x A in a finite group satisfies phi_*(beta alpha - 1) = 0.
A window (A, B) is dead once the finite images found are jointly injective on the cells
BA u {1}. Otherwise the defect is confined to the surviving classes: the cells that every image
merges.

Table group U(A, B): one generator x_g per cell g in C = A u B u AB u BA, with x_1 = 1 and
relators x_a x_b = x_(ab) and x_b x_a = x_(ba).

Stage 1: characters U -> Z/p for the primes in --primes, via a sparse reduced echelon form over
F_p with pivots at the later cells. A pivot cell's normal form is minus its row off the pivot;
a free cell's normal form is itself. The partition of BA u {1} by normal form is refined across
primes. The separating characters are stored, and --verify replays them against every relator.

Stage 2: GAP (on MSI: module load sagemath/10.7; sage -gap -q file.g). First the presentation is
compacted: each cell that is the product of two earlier cells is replaced by that product, so the
generators are the undefined cells. The GAP file then enumerates quotients onto small simple groups
and low-index coset actions, and writes each image as permutations of the compact generators.
--verify replays every relator of U(A, B) and refines the partition.

Usage (MSI, shared library as in gottschalk-small-presentations/window_table_screen.py):
  python df_table_screen.py --windows v:1:1,atlas:1:1 --out res.json --gap-dir gap/
  sage -gap -q gap/v-1-1.g
  python df_table_screen.py --verify res.json --gap-dir gap/
"""
import argparse
import json
import os
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get(
    "LEAVITT_LIB",
    "/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/experiments/nonsofic-certificates"))
sys.path.insert(0, os.path.join(HERE, "..", "sat"))
import leavitt as L  # noqa: E402
import dfsat  # noqa: E402

if hasattr(L, "set_dual"):
    L.set_dual(False)


def family_gens(fam):
    if fam == "v-eld1":   # Thompson V together with the E_ij(1) of the nine-leaf corner and u, v
        gens = dict(dfsat.generators(L, "v"))
        gens.update({k: u for k, u in dfsat.generators(L, "eld").items() if k.endswith("_1") or k in ("u", "v")})
        return gens
    return dfsat.generators(L, fam)


def table(fam, ra, rb):
    gens = family_gens(fam)
    A = dfsat.ball(L, gens, ra)
    B = A if ra == rb else dfsat.ball(L, gens, rb)
    index, cells = {}, []

    def idx(u):
        if u.key not in index:
            index[u.key] = len(cells)
            cells.append(u)
        return index[u.key]
    idx(L.IDENTITY)
    for u in list(A) + list(B):
        idx(u)
    rels, ba = set(), {0}
    for a in A:
        for b in B:
            rels.add((index[a.key], index[b.key], idx(a * b)))
            k = idx(b * a)
            rels.add((index[b.key], index[a.key], k))
            ba.add(k)
    return len(A), len(B), cells, sorted(rels), sorted(ba)


def rref(rels, p):
    """piv[c] = row with pivot c (entry 1); every other entry is at a free column."""
    piv, users = {}, defaultdict(set)
    for i, j, k in rels:
        row = defaultdict(int)
        for c, s in ((i, 1), (j, 1), (k, p - 1)):
            if c:
                row[c] = (row[c] + s) % p
        for c in [c for c in row if c in piv and row[c]]:
            f = row.pop(c)
            for d, v in piv[c].items():
                if d != c:
                    row[d] = (row[d] - f * v) % p
        row = {c: v for c, v in row.items() if v}
        if not row:
            continue
        c = max(row)
        inv = pow(row[c], p - 2, p)
        row = {d: v * inv % p for d, v in row.items()}
        for r in list(users.pop(c, ())):
            f = piv[r].pop(c)
            for d, v in row.items():
                if d == c:
                    continue
                nv = (piv[r].get(d, 0) - f * v) % p
                if nv:
                    piv[r][d] = nv
                    users[d].add(r)
                elif d in piv[r]:
                    del piv[r][d]
                    users[d].discard(r)
        piv[c] = row
        for d in row:
            if d != c:
                users[d].add(c)
    return piv, users


def classes(keys):
    """Cells grouped by equal key; returns the classes with more than one cell."""
    by = defaultdict(list)
    for g, key in keys.items():
        by[key].append(g)
    return sorted(sorted(v) for v in by.values() if len(v) > 1)


def stage1(rels, ba, primes):
    keys = {g: () for g in ba}
    chars = []
    for p in primes:
        piv, users = rref(rels, p)
        free = set()
        for g in ba:
            if g in piv:
                free.update(f for f in piv[g] if f != g)
            elif g:
                free.add(g)
        for f in sorted(free):
            chi = {f: 1}
            chi.update({c: (-piv[c][f]) % p for c in users.get(f, ())})
            new = {g: keys[g] + (chi.get(g, 0),) for g in ba}
            if len(set(new.values())) > len(set(keys.values())):
                keys = new
                chars.append({"p": p, "chi": sorted(chi.items())})
    return keys, chars


def compact(cells, rels):
    """Words in the undefined cells: def(k) = (i, j) with i, j < k and x_i x_j = x_k, shortest first."""
    cands = defaultdict(list)
    for i, j, k in rels:
        if i < k and j < k:
            cands[k].append((i, j))
    word, basic = {0: []}, []
    for k in range(1, len(cells)):
        best = min(cands.get(k, ()), key=lambda ij: len(word[ij[0]]) + len(word[ij[1]]), default=None)
        if best is None:
            basic.append(k)
            word[k] = [(len(basic), 1)]
        else:
            word[k] = word[best[0]] + word[best[1]]
    out = set()
    for i, j, k in rels:
        w = word[i] + word[j] + [(g, -e) for g, e in reversed(word[k])]
        red = []
        for letter in w:
            if red and red[-1] == (letter[0], -letter[1]):
                red.pop()
            else:
                red.append(letter)
        if red:
            out.add(tuple(red))
    return basic, word, sorted(out)


def gap_file(path, wit, nbasic, crels, max_index):
    def w(r):
        return "*".join("g[%d]%s" % (a, "" if e == 1 else "^-1") for a, e in r)
    with open(path, "w") as fh:
        fh.write("F := FreeGroup(%d);; g := GeneratorsOfGroup(F);;\nrels := [%s];;\n" % (
            nbasic, ",\n".join(w(r) for r in crels)))
        fh.write("U := F/rels;; iso := IsomorphismSimplifiedFpGroup(U);; V := Range(iso);;\n"
                 "Print(\"SIMPLIFIED \", Length(GeneratorsOfGroup(V)), \" \", Length(RelatorsOfFpGroup(V)), \"\\n\");\n"
                 "out := OutputTextFile(\"%s\", false);; SetPrintFormattingStatus(out, false);;\n"
                 "emit := function(hom, deg, tag) local imgs;\n"
                 "  imgs := List(GeneratorsOfGroup(U), x -> Image(hom, Image(iso, x)));\n"
                 "  AppendTo(out, \"{\\\"tag\\\": \\\"\", tag, \"\\\", \\\"degree\\\": \", deg,\n"
                 "    \", \\\"perms\\\": \", List(imgs, x -> ListPerm(x, deg)), \"}\\n\");\nend;;\n" % wit)
        fh.write("targets := [[AlternatingGroup(5), \"A5\"], [PSL(3,2), \"PSL(3,2)\"], [AlternatingGroup(6), \"A6\"],\n"
                 "  [PSL(2,8), \"PSL(2,8)\"], [PSL(2,11), \"PSL(2,11)\"], [PSL(2,13), \"PSL(2,13)\"],\n"
                 "  [AlternatingGroup(7), \"A7\"], [AlternatingGroup(8), \"A8\"]];;\n"
                 "for T in targets do for hom in GQuotients(V, T[1]) do\n"
                 "  emit(hom, LargestMovedPoint(T[1]), T[2]); od; Print(\"DONE \", T[2], \"\\n\"); od;\n"
                 "for K in LowIndexSubgroupsFpGroup(V, %d) do if Index(V, K) > 1 then\n"
                 "  emit(FactorCosetAction(V, K), Index(V, K), \"cosets\"); fi; od;\n"
                 "CloseStream(out);; Print(\"GAP_DONE\\n\");\nQUIT;\n" % max_index)


def mul(g, h):
    return [h[x] for x in g]


def replay_images(cells, rels, ba, word, wit_path, keys):
    """Apply every GAP image: check all relators of U(A, B), then refine the keys on BA u {1}."""
    used = bad = 0
    for line in open(wit_path):
        rec = json.loads(line)
        n = rec["degree"]
        gens = [[x - 1 for x in p] + list(range(len(p), n)) for p in rec["perms"]]
        inv = [[0] * n for _ in gens]
        for a, p in enumerate(gens):
            for x, y in enumerate(p):
                inv[a][y] = x
        perm = {}
        for k in range(len(cells)):
            img = list(range(n))
            for a, e in word[k]:
                img = mul(img, gens[a - 1] if e == 1 else inv[a - 1])
            perm[k] = tuple(img)
        if any(mul(perm[i], perm[j]) != list(perm[k]) for i, j, k in rels):
            bad += 1
            continue
        used += 1
        keys = {g: keys[g] + (perm[g],) for g in ba}
    return keys, used, bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--windows", default="v:1:1")
    ap.add_argument("--primes", default="2,3,5,7,1000003")
    ap.add_argument("--max-index", type=int, default=6)
    ap.add_argument("--out")
    ap.add_argument("--gap-dir")
    ap.add_argument("--verify")
    args = ap.parse_args()
    if args.verify:
        results = json.load(open(args.verify))
        for rec in results:
            nA, nB, cells, rels, ba = table(rec["family"], rec["ra"], rec["rb"])
            keys = {g: () for g in ba}
            ok = True
            for ch in rec["characters"]:
                p, chi = ch["p"], dict(ch["chi"])
                ok &= all((chi.get(i, 0) + chi.get(j, 0) - chi.get(k, 0)) % p == 0 for i, j, k in rels)
                keys = {g: keys[g] + (chi.get(g, 0),) for g in ba}
            rec["stage1_classes_replayed"] = len(classes(keys))
            tag = "%s-%d-%d" % (rec["family"], rec["ra"], rec["rb"])
            wit = os.path.join(args.gap_dir or ".", tag + ".witness.jsonl")
            if os.path.exists(wit):
                basic, word, crels = compact(cells, rels)
                keys, used, bad = replay_images(cells, rels, ba, word, wit, keys)
                rec.update(images_used=used, images_rejected=bad)
            cl = classes(keys)
            rec.update(characters_ok=ok, final_classes=len(cl), final_class_sizes=sorted(len(c) for c in cl),
                       final_classes_cells=cl, status="DEAD" if ok and not cl else "SURVIVES")
            print(tag, {k: rec[k] for k in ("characters_ok", "stage1_classes", "final_classes", "status")
                        if k in rec}, flush=True)
        json.dump(results, open(args.verify.replace(".json", ".final.json"), "w"))
        return
    primes = [int(x) for x in args.primes.split(",")]
    results = []
    for spec in args.windows.split(","):
        fam, ra, rb = spec.split(":")
        ra, rb = int(ra), int(rb)
        nA, nB, cells, rels, ba = table(fam, ra, rb)
        keys, chars = stage1(rels, ba, primes)
        cl = classes(keys)
        rec = {"family": fam, "ra": ra, "rb": rb, "A": nA, "B": nB, "cells": len(cells), "relators": len(rels),
               "ba_cells": len(ba), "stage1_classes": len(cl), "stage1_class_sizes": sorted(len(c) for c in cl),
               "characters": chars}
        if cl and args.gap_dir:
            os.makedirs(args.gap_dir, exist_ok=True)
            basic, word, crels = compact(cells, rels)
            tag = "%s-%d-%d" % (fam, ra, rb)
            gap_file(os.path.join(args.gap_dir, tag + ".g"), os.path.join(args.gap_dir, tag + ".witness.jsonl"),
                     len(basic), crels, args.max_index)
            rec.update(compact_generators=len(basic), compact_relators=len(crels))
        print(spec, {k: v for k, v in rec.items() if k != "characters"}, flush=True)
        results.append(rec)
    if args.out:
        json.dump(results, open(args.out, "w"))


if __name__ == "__main__":
    main()
