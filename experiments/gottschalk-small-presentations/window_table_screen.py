"""Rule-free screen of invariant-output windows over R^x = L_{F_2}(1,2)^x.

Setting (research/strict-pairs-transfer-to-table-realizations.md, Corollary 3, and
Theorem F of research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md).
A window is (S, M, H) with H = <h> finite cyclic, 1 in S and M, and HM = M. Its
table group U has a generator x_a per a in S u M (x_1 = 1) and relators

    x_s x_m = x_s' x_m'   whenever s m = s' m'   (s, s' in S; m, m' in M),
    x_k x_m = x_(k m)     for k in H, m in M.

If some homomorphism from U into a finite group sends x_h to a nontrivial element,
no pair of local rules on the window is strict, whatever the rules.

Stage 1: characters U -> Z/p (p = order of h, prime) with chi(x_h) != 0, by linear
algebra over F_p; the character is stored as a replayable witness.
Stage 2: for stage-1 survivors a GAP file (Tietze simplification, then permutation
images from low-index subgroups). A separating image is stored as permutation
images of the original generators, relator-checked in GAP and replayed by --verify.

MSI usage (shared env):
  python window_table_screen.py --out results.json --gap-dir gap/
  sage -gap -q gap/<window>.g          # writes gap/<window>.witness.json
  python window_table_screen.py --verify results.json --gap-dir gap/
"""

import argparse
import itertools
import json
import os
import sys

sys.path.insert(0, os.environ.get(
    "LEAVITT_LIB",
    "/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/experiments/nonsofic-certificates"))
import leavitt as L  # noqa: E402


def named_units():
    su = L.standard_units()
    U = {"u": su["@u"], "v": su["@v"], "w": su["@w"], "g": su["@g"]}
    U["G"] = U["g"].inverse()
    tu = L.thompson_unit
    U["a"] = tu(["0", "10", "11"], ["00", "01", "1"])
    U["A"] = U["a"].inverse()
    U["t"] = L.one_plus_nilpotent(L.S("00") * L.T("01"))
    U["q"] = L.one_plus_nilpotent(L.S("1") * L.T("01"))
    U["r"] = L.one_plus_nilpotent(L.S("01") * L.T("1"))
    # OpenAI nine-leaf triple (as in kaplansky-df/sat/dfsat.py, family eld)
    alpha, beta = ["000", "001", "01"], ["1000", "1001", "101"]
    nu, zeta = ["1100", "1101", "111"], ["100", "101", "11"]
    ring = {"1": L.ONE, "s0": L.s0, "s1": L.s1, "t0": L.t0, "t1": L.t1}
    for i, j in itertools.permutations(range(3), 2):
        for name, x in ring.items():
            U["E%d%d_%s" % (i, j, name)] = L.one_plus_nilpotent(L.S(alpha[i]) * x * L.T(alpha[j]))
    dom = alpha + beta + nu
    U["cu"] = tu(dom, [x + "0" for x in alpha] + [x + "1" for x in alpha] + zeta)
    U["cv"] = tu(dom, [x + "0" for x in alpha] + zeta + [x + "1" for x in alpha])
    U["p3"] = L.corner_matrix_unit(alpha, [2, 4, 1])   # 3-cycle of the alpha leaves
    # the two GL(4,2) atlas charts of dfsat.py (generate all of R^x)
    leaves = {1: ["01", "1", "000", "001"], 2: ["00", "1", "010", "011"]}
    adjacent = [(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)]
    for f in (1, 2):
        for word in ((0, 1, 2), (3, 5, 4)):
            m = [[int(i == j) for j in range(4)] for i in range(4)]
            for index in word:
                rr, cc = adjacent[index]
                t = [[int(i == j) for j in range(4)] for i in range(4)]
                t[rr][cc] ^= 1
                m = [[sum(m[i][k] & t[k][j] for k in range(4)) & 1 for j in range(4)] for i in range(4)]
            cols = [sum(m[i][j] << i for i in range(4)) for j in range(4)]
            U["ch%d_%s" % (f, "".join(map(str, word)))] = L.corner_matrix_unit(leaves[f], cols)
    return U


ELD1 = ["E%d%d_1" % ij for ij in itertools.permutations(range(3), 2)]
ELDR = ["E%d%d_%s" % (i, j, n) for i, j in itertools.permutations(range(3), 2)
        for n in ("1", "s0", "s1", "t0", "t1")]
ATLAS = ["ch1_012", "ch1_354", "ch2_012", "ch2_354"]
FAMILIES = {
    "control-gl2": (["u", "v", "w"], "u"),
    "v-plus-swap": (["w", "a", "A"], "w"),
    "transvections-depth12": (["u", "v", "t", "q", "r"], "u"),
    "transvections-swap": (["w", "t", "q", "r"], "w"),
    "order3-thompson": (["g", "G", "a", "A"], "g"),
    "order3-transvections": (["g", "G", "t", "q", "r"], "g"),
    "mixed-all": (["u", "v", "w", "a", "A", "t", "q", "r"], "u"),
    "mixed-all-order3": (["g", "G", "w", "a", "A", "t", "q", "r"], "g"),
    "atlas-order2": (ATLAS, "u"),
    "atlas-order3": (ATLAS, "g"),
    "eld1-compressors-order2": (ELD1 + ["cu", "cv"], "E01_1"),
    "eld1-compressors-order3": (ELD1 + ["cu", "cv", "p3"], "p3"),
    "eld-full-order2": (ELDR + ["cu", "cv"], "E01_1"),
}


def ball(gens, radius):
    steps = []
    for x in gens:
        steps.append(x)
        if x.inverse().key != x.key:
            steps.append(x.inverse())
    elems = {L.IDENTITY.key: L.IDENTITY}
    frontier = [L.IDENTITY]
    for _ in range(radius):
        nxt = []
        for x in frontier:
            for s in steps:
                y = x * s
                if y.key not in elems:
                    elems[y.key] = y
                    nxt.append(y)
        frontier = nxt
    return elems


def window(units, gen_names, h_name, r_m, r_s):
    gens = [units[n] for n in gen_names]
    h = units[h_name]
    order = h.order(limit=12)
    powers = [h ** i for i in range(order)]
    M = {}
    for k in powers:
        for m in ball(gens, r_m).values():
            y = k * m
            M.setdefault(y.key, y)
    return h, order, powers, ball(gens, r_s), M


def relators(h, powers, S, M):
    keys = sorted(set(S) | set(M), key=repr)
    ident = L.IDENTITY.key
    index = {k: i for i, k in enumerate(k for k in keys if k != ident)}

    def word(*ks):
        return [index[k] for k in ks if k != ident]
    by_product = {}
    for s_key, s in S.items():
        for m_key, m in M.items():
            by_product.setdefault((s * m).key, []).append((s_key, m_key))
    rels = []
    for pairs in by_product.values():
        for s1, m1 in pairs[1:]:
            rels.append((word(*pairs[0]), word(s1, m1)))
    for k in powers[1:]:
        for m_key, m in M.items():
            rels.append((word(k.key, m_key), word((k * m).key)))
    return index, rels, index[h.key]


def character_escape(rels, n, h_idx, p):
    """chi over F_p with chi.rel = 0 on every relator and chi[h] != 0, or None."""
    piv = {}
    for lhs, rhs in rels:
        row = {}
        for c, sgn in [(c, 1) for c in lhs] + [(c, -1) for c in rhs]:
            row[c] = (row.get(c, 0) + sgn) % p
        row = {c: v for c, v in row.items() if v}
        while row:
            c = min(row)
            if c not in piv:
                inv = pow(row[c], p - 2, p)
                piv[c] = {cc: vv * inv % p for cc, vv in row.items()}
                break
            f = row[c]
            for cc, vv in piv[c].items():
                row[cc] = (row.get(cc, 0) - f * vv) % p
            row = {cc: vv for cc, vv in row.items() if vv}
    for c in sorted(piv, reverse=True):
        for d in piv:
            if d != c and c in piv[d]:
                f = piv[d][c]
                for cc, vv in piv[c].items():
                    piv[d][cc] = (piv[d].get(cc, 0) - f * vv) % p
                piv[d] = {cc: vv for cc, vv in piv[d].items() if vv}
    free = [c for c in range(n) if c not in piv]
    for f in free:
        if f == h_idx or piv.get(h_idx, {}).get(f, 0):
            chi = [0] * n
            chi[f] = 1
            for c, row in piv.items():
                chi[c] = (-row.get(f, 0)) % p
            if chi[h_idx]:
                return chi
    return None


def check_chi(rels, chi, h_idx, p):
    return chi[h_idx] % p != 0 and all(
        (sum(chi[c] for c in l) - sum(chi[c] for c in r)) % p == 0 for l, r in rels)


def perm_word(perms, word, npts):
    img = list(range(npts))
    for c in word:
        img = [perms[c][i] - 1 for i in img]
    return img


def check_perm_witness(rels, perms, h_idx, npts):
    perms = [p + list(range(len(p) + 1, npts + 1)) for p in perms]
    if perm_word(perms, [h_idx], npts) == list(range(npts)):
        return False
    return all(perm_word(perms, l, npts) == perm_word(perms, r, npts) for l, r in rels)


def gap_file(path, n, rels, h_idx, max_index):
    def w(ix):
        return "*".join("F.%d" % (i + 1) for i in ix) if ix else "One(F)"
    wit = path[:-2] + ".witness.json"
    with open(path, "w") as fh:
        fh.write("F := FreeGroup(%d);;\nrels := [%s];;\n" % (
            n, ",\n".join("%s/(%s)" % (w(l), w(r)) for l, r in rels)))
        fh.write("U := F/rels;;\niso := IsomorphismSimplifiedFpGroup(U);;\nV := Range(iso);;\n"
                 "yh := Image(iso, U.%d);;\nres := \"SURVIVES_TO_INDEX_%d\";;\n" % (h_idx + 1, max_index))
        fh.write("for K in LowIndexSubgroupsFpGroup(V, %d) do\n"
                 "  hom := FactorCosetAction(V, K);;\n"
                 "  if Image(hom, yh) <> () then\n"
                 "    imgs := List(GeneratorsOfGroup(U), x -> Image(hom, Image(iso, x)));;\n"
                 "    ok := ForAll(rels, rr -> MappedWord(rr, GeneratorsOfGroup(F), imgs) = ());;\n"
                 "    out := OutputTextFile(\"%s\", false);; SetPrintFormattingStatus(out, false);;\n"
                 "    PrintTo(out, \"{\\\"index\\\": \", Index(V, K), \", \\\"gap_relators_ok\\\": \",\n"
                 "      ok, \", \\\"perms\\\": \", List(imgs, x -> ListPerm(x, Index(V, K))), \"}\\n\");;\n"
                 "    CloseStream(out);;\n"
                 "    res := Concatenation(\"SEP_INDEX_\", String(Index(V, K)));; break;\n"
                 "  fi;\nod;\nPrint(\"RESULT \", res, \"\\n\");\nQUIT;\n" % (max_index, wit))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    ap.add_argument("--gap-dir")
    ap.add_argument("--families", default=",".join(FAMILIES))
    ap.add_argument("--radii", default="1:1,1:2,2:1,2:2")
    ap.add_argument("--max-index", type=int, default=6)
    ap.add_argument("--verify")
    args = ap.parse_args()
    units = named_units()
    if args.verify:
        bad = 0
        for rec in json.load(open(args.verify)):
            h, order, powers, S, M = window(units, rec["gens"], rec["h"], rec["r_m"], rec["r_s"])
            index, rels, h_idx = relators(h, powers, S, M)
            tag = "%s-%d-%d" % (rec["family"], rec["r_m"], rec["r_s"])
            if rec["stage1"] == "separated":
                ok, how = check_chi(rels, rec["chi"], h_idx, rec["p"]), "character mod %d" % rec["p"]
            else:
                wpath = os.path.join(args.gap_dir or ".", tag + ".witness.json")
                if not os.path.exists(wpath):
                    print(tag, "NO WITNESS")
                    bad += 1
                    continue
                wit = json.loads(open(wpath).read().replace("true", "1").replace("false", "0"))
                ok = bool(wit["gap_relators_ok"]) and check_perm_witness(rels, wit["perms"], h_idx, wit["index"])
                how = "permutation image of degree %d" % wit["index"]
            bad += not ok
            print(tag, how, "OK" if ok else "FAIL")
        sys.exit(1 if bad else 0)
    radii = [tuple(int(x) for x in rr.split(":")) for rr in args.radii.split(",")]
    results = []
    for fam, (r_m, r_s) in itertools.product(args.families.split(","), radii):
        gens, h_name = FAMILIES[fam]
        h, order, powers, S, M = window(units, gens, h_name, r_m, r_s)
        index, rels, h_idx = relators(h, powers, S, M)
        n = len(index)
        rec = {"family": fam, "gens": gens, "h": h_name, "order": order, "r_m": r_m, "r_s": r_s,
               "S": len(S), "M": len(M), "generators": n, "relators": len(rels), "p": order}
        chi = character_escape(rels, n, h_idx, order) if order in (2, 3, 5, 7) else None
        if chi is not None and check_chi(rels, chi, h_idx, order):
            rec.update(stage1="separated", chi=chi)
        else:
            rec.update(stage1="survives")
            if args.gap_dir:
                os.makedirs(args.gap_dir, exist_ok=True)
                gap_file(os.path.join(args.gap_dir, "%s-%d-%d.g" % (fam, r_m, r_s)), n, rels, h_idx,
                         args.max_index)
        print(fam, "r_m=%d r_s=%d |S|=%d |M|=%d gens=%d rels=%d -> %s" % (
            r_m, r_s, len(S), len(M), n, len(rels), rec["stage1"]), flush=True)
        results.append(rec)
    if args.out:
        json.dump(results, open(args.out, "w"))


if __name__ == "__main__":
    main()
