"""Rule-free screen of GENERAL automaton designs over R^x = L_{F_2}(1,2)^x.

A window is (S, M) with 1 in S and M. Local rules nu on S and mu on M give
tau(x)(g) = mu(x|gM) and sigma(y)(g) = nu(y|gS) over G = R^x.

Criterion (research/two-rectangle-surjunctive-images-kill-all-designs.md):
let T be the group with a letter x_a for each a in S u M (x_1 = 1) and relators

    x_s x_m = x_s' x_m'   whenever s m = s' m' in G   (S x M rectangle),
    x_m x_s = x_m' x_s'   whenever m s = m' s' in G   (M x S rectangle).

If homomorphisms from T into finite groups separate every pair of G-distinct
products m s, m' s' (m, m' in M; s, s' in S), then no design on (S, M), over any
alphabet, is a strict pair over G.

Stage 0: if S u M generates a finite subgroup of G, the window is dead (the
inclusion is the finite realization).
Stage 1: GAP file. Simplify T, then run through GQuotients onto small simple
groups and permutation actions on low-index subgroups, keeping each image that
separates more M x S classes. Witness: permutation images of the original
letters. --verify replays every witness in Python (relators and separation).

MSI:
  python3 general_window_screen.py --out res.json --gap-dir gap/
  sage -gap -q gap/<window>.g
  python3 general_window_screen.py --verify res.json --gap-dir gap/
"""

import argparse
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get(
    "SMALLPRES", os.path.join(HERE, "..", "gottschalk-small-presentations")))
import window_table_screen as W  # noqa: E402
L = W.L


def extra_units(U):
    tu = L.thompson_unit
    rest = ["0", "11", "101", "1001"]
    # c in J = V_(1000): x_0 of Thompson's F on the cylinder [1000]
    U["c"] = tu(rest + ["10000", "100010", "100011"], rest + ["100000", "100001", "10001"])
    U["C"] = U["c"].inverse()
    U["CU"] = U["cu"].inverse()
    U["CV"] = U["cv"].inverse()
    # compressed conjugate a = u c^-1 u^-1 lies in V_(0001) <= Gamma
    U["ca"] = U["cu"] * U["C"] * U["CU"]
    U["CA"] = U["ca"].inverse()
    return U


def defect_element(U, l_name):
    x = U["cu"] * U["c"] * U["CU"]
    return x * U[l_name] * x.inverse() * U[l_name].inverse()


def finite_closure(elems, limit=20000):
    seen = {e.key: e for e in elems}
    seen[L.IDENTITY.key] = L.IDENTITY
    frontier = list(seen.values())
    gens = list(elems)
    while frontier:
        nxt = []
        for x in frontier:
            for s in gens:
                y = x * s
                if y.key not in seen:
                    seen[y.key] = y
                    nxt.append(y)
                    if len(seen) > limit:
                        return None
        frontier = nxt
    return len(seen)


def tables(S, M):
    keys = sorted(set(S) | set(M), key=repr)
    ident = L.IDENTITY.key
    index = {k: i for i, k in enumerate(k for k in keys if k != ident)}

    def word(*ks):
        return [index[k] for k in ks if k != ident]
    rels = []
    classes = {}
    for left, right, store in ((S, M, None), (M, S, classes)):
        by_product = {}
        for a_key, a in left.items():
            for b_key, b in right.items():
                by_product.setdefault((a * b).key, []).append((a_key, b_key))
        for pairs in by_product.values():
            for a1, b1 in pairs[1:]:
                rels.append((word(*pairs[0]), word(a1, b1)))
        if store is not None:
            for prod_key, pairs in by_product.items():
                store[prod_key] = word(*pairs[0])
    return index, rels, list(classes.values())


def gap_word(ix):
    return "*".join("F.%d" % (i + 1) for i in ix) if ix else "One(F)"


def gap_file(path, n, rels, classes, max_index):
    wit = path[:-2] + ".witness.json"
    with open(path, "w") as fh:
        fh.write("F := FreeGroup(%d);;\nrels := [%s];;\n" % (
            n, ",\n".join("%s/(%s)" % (gap_word(l), gap_word(r)) for l, r in rels) or ""))
        fh.write("cls := [%s];;\n" % ",\n".join(gap_word(c) for c in classes))
        fh.write("U := F/rels;;\niso := IsomorphismSimplifiedFpGroup(U);;\nV := Range(iso);;\n"
                 "Print(\"SIMPLIFIED gens \", Length(GeneratorsOfGroup(V)), \" rels \",\n"
                 "  Length(RelatorsOfFpGroup(V)), \"\\n\");\n"
                 "sig := List(cls, c -> []);; reps := [];;\n"
                 "nsep := function(s) return Length(Set(s)); end;;\n"
                 "tryhom := function(hom, tag)\n"
                 "  local imgs, vals, news, deg;\n"
                 "  imgs := List(GeneratorsOfGroup(U), x -> Image(hom, Image(iso, x)));\n"
                 "  vals := List(cls, c -> MappedWord(c, GeneratorsOfGroup(F), imgs));\n"
                 "  news := List([1..Length(cls)], i -> Concatenation(sig[i], [vals[i]]));\n"
                 "  if nsep(news) > nsep(sig) then\n"
                 "    sig := news;\n"
                 "    deg := Maximum(Concatenation([1], List(imgs, LargestMovedPoint)));\n"
                 "    Add(reps, rec(tag := tag, deg := deg, perms := List(imgs, x -> ListPerm(x, deg))));\n"
                 "  fi;\nend;;\n")
        fh.write("targets := [[PSL(3,2), \"PSL(3,2)\"], [AlternatingGroup(5), \"A5\"],\n"
                 "  [AlternatingGroup(6), \"A6\"], [AlternatingGroup(7), \"A7\"], [PSL(2,8), \"PSL(2,8)\"],\n"
                 "  [PSL(2,11), \"PSL(2,11)\"], [SymmetricGroup(4), \"S4\"], [SymmetricGroup(5), \"S5\"]];;\n"
                 "for T in targets do\n"
                 "  if nsep(sig) < Length(cls) then\n"
                 "    for hom in GQuotients(V, T[1]) do\n"
                 "      if nsep(sig) < Length(cls) then tryhom(hom, T[2]); fi;\n"
                 "    od;\n  fi;\nod;\n")
        fh.write("if nsep(sig) < Length(cls) then\n"
                 "  it := LowIndexSubgroupsFpGroupIterator(V, TrivialSubgroup(V), %d);; seen := 0;;\n"
                 "  while nsep(sig) < Length(cls) and not IsDoneIterator(it) and seen < 50000 do\n"
                 "    K := NextIterator(it);; seen := seen + 1;;\n"
                 "    if Index(V, K) > 1 then\n"
                 "      tryhom(FactorCosetAction(V, K), Concatenation(\"cosets\", String(Index(V, K))));\n"
                 "    fi;\n  od;\n  Print(\"LOWINDEX seen \", seen, \"\\n\");\nfi;\n" % max_index)
        fh.write("out := OutputTextFile(\"%s\", false);; SetPrintFormattingStatus(out, false);;\n"
                 "PrintTo(out, \"{\\\"classes\\\": \", Length(cls), \", \\\"separated\\\": \", nsep(sig),\n"
                 "  \", \\\"reps\\\": [\");\n"
                 "for i in [1..Length(reps)] do\n"
                 "  if i > 1 then AppendTo(out, \", \"); fi;\n"
                 "  AppendTo(out, \"{\\\"tag\\\": \\\"\", reps[i].tag, \"\\\", \\\"deg\\\": \", reps[i].deg,\n"
                 "    \", \\\"perms\\\": \", reps[i].perms, \"}\");\nod;\n"
                 "AppendTo(out, \"]}\\n\");\nCloseStream(out);\n"
                 "Print(\"RESULT \", nsep(sig), \" of \", Length(cls), \"\\n\");\nQUIT;\n" % wit)


def perm_word(perms, word, npts):
    img = list(range(npts))
    for c in word:
        img = [perms[c][i] - 1 for i in img]
    return tuple(img)


def verify_witness(rels, classes, wit):
    sigs = [[] for _ in classes]
    for rep in wit["reps"]:
        npts = max([rep["deg"]] + [len(p) for p in rep["perms"]])
        perms = [p + list(range(len(p) + 1, npts + 1)) for p in rep["perms"]]
        if not all(perm_word(perms, l, npts) == perm_word(perms, r, npts) for l, r in rels):
            return None
        for i, c in enumerate(classes):
            sigs[i].append(perm_word(perms, c, npts))
    return len(set(tuple(s) for s in sigs))


def windows(U):
    X_T = ["a", "A", "w"]
    X_TR = ["u", "v", "t", "q", "r"]
    E1 = W.ELD1
    d01 = defect_element(U, "E01_1")
    U["d01"] = d01
    ball = lambda gens, r: W.ball([U[n] for n in gens], r)
    pick = lambda names: {U[n].key: U[n] for n in ["e"] + names}
    U["e"] = L.IDENTITY
    out = {
        "control-gl2-1-1": (ball(["u", "v", "w"], 1), ball(["u", "v", "w"], 1)),
        "thompson-aw-1-1": (ball(X_T, 1), ball(X_T, 1)),
        "thompson-aw-2-1": (ball(X_T, 2), ball(X_T, 1)),
        "thompson-aw-1-2": (ball(X_T, 1), ball(X_T, 2)),
        "transvections-1-1": (ball(X_TR, 1), ball(X_TR, 1)),
        "eld1-cu-1-1": (ball(E1 + ["cu"], 1), ball(E1 + ["cu"], 1)),
        "eld1-cu-c-1-1": (ball(E1 + ["cu", "c"], 1), ball(E1 + ["cu", "c"], 1)),
        # most direct defect design: rooted identification (a l^-1, l) ~ (1, a)
        "defect-direct-E01": (pick(["ca", "CA"]) | {(U["ca"] * U["E01_1"].inverse()).key:
                                                    U["ca"] * U["E01_1"].inverse()},
                              pick(["E01_1", "ca"])),
        "defect-nested-E01": (pick(["ca", "cu", "CU", "c"]) | {(U["ca"] * U["E01_1"].inverse()).key:
                                                             U["ca"] * U["E01_1"].inverse()},
                              pick(["E01_1", "ca", "cu", "c", "d01"])),
        "defect-ball-1-1": (ball(["E01_1", "cu", "c"], 1), ball(["E01_1", "cu", "c", "d01"], 1)),
    }
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    ap.add_argument("--gap-dir")
    ap.add_argument("--only", default="")
    ap.add_argument("--max-index", type=int, default=6)
    ap.add_argument("--verify")
    args = ap.parse_args()
    U = extra_units(W.named_units())
    wins = windows(U)
    if args.only:
        wins = {k: v for k, v in wins.items() if k in args.only.split(",")}
    if args.verify:
        res = json.load(open(args.verify))
        for name, row in res.items():
            if row["stage"] != "gap":
                continue
            S, M = wins[name]
            _, rels, classes = tables(S, M)
            p = os.path.join(args.gap_dir, name + ".witness.json")
            if not os.path.exists(p):
                row["verified"] = "NO_WITNESS"
                continue
            sep = verify_witness(rels, classes, json.load(open(p)))
            row["verified_separated"] = sep
            row["verdict"] = "DEAD" if sep == len(classes) else "SURVIVES_WITHIN_BOUND"
            print(name, row["verdict"], sep, "of", len(classes))
        json.dump(res, open(args.verify, "w"), indent=1)
        return
    os.makedirs(args.gap_dir, exist_ok=True)
    res = {}
    for name, (S, M) in wins.items():
        order = finite_closure(list(S.values()) + list(M.values()))
        index, rels, classes = tables(S, M)
        row = {"S": len(S), "M": len(M), "letters": len(index), "relators": len(rels),
               "ms_classes": len(classes), "finite_subgroup_order": order}
        if name.startswith("defect"):
            row["d01_nontrivial"] = not U["d01"].is_identity()
        if order is not None:
            row["stage"], row["verdict"] = "finite", "DEAD"
        else:
            row["stage"] = "gap"
            gap_file(os.path.join(args.gap_dir, name + ".g"), len(index), rels, classes,
                     args.max_index)
        res[name] = row
        print(name, row)
    json.dump(res, open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
