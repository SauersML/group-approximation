"""Rule-free screen of invariant-output windows over R^x = L_{F_2}(1,2)^x.

Setting (research/strict-pairs-transfer-to-table-realizations.md, Corollary 3, and
Theorem F of research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md).
A window is (S, M, H) with H = <h> a finite cyclic subgroup, 1 in S and M, and
HM = M. Its table group U has one generator x_a per a in S u M (x_1 = 1) and
relators

    x_s x_m = x_s' x_m'   whenever s m = s' m'   (s, s' in S; m, m' in M),
    x_k x_m = x_(k m)     for k in H, m in M.

If some homomorphism from U into a surjunctive group sends x_h to a nontrivial
element, no pair of local rules on the window is strict, whatever the rules.

Stage 1 (this script): abelian images.  A character chi: U -> Z/p, p = order of h
(prime), is a vector over F_p vanishing on every relator vector.  If e_h is not
in the F_p row space of the relator matrix, a chi with chi(x_h) = 1 exists; it is
written out as a replayable witness and the window is dead.
Stage 2: surviving windows get a GAP file (Tietze simplification, low-index
permutation images) under --gap-dir.

Usage (MSI, shared env):
  LEAVITT_LIB=/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/experiments/nonsofic-certificates \\
  python window_table_screen.py --out results.json --gap-dir gap/
  python window_table_screen.py --verify results.json
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
    units = {"u": su["@u"], "v": su["@v"], "w": su["@w"], "g": su["@g"]}
    units["G"] = units["g"].inverse()
    a = L.thompson_unit(["0", "10", "11"], ["00", "01", "1"])   # infinite order, in V
    units["a"] = a
    units["A"] = a.inverse()
    units["t"] = L.one_plus_nilpotent(L.S("00") * L.T("01"))  # depth-two transvection
    units["q"] = L.one_plus_nilpotent(L.S("1") * L.T("01"))   # mixes depths one and two
    units["r"] = L.one_plus_nilpotent(L.S("01") * L.T("1"))
    return units


def ball(gens, radius):
    elems = {L.IDENTITY.key: L.IDENTITY}
    frontier = [L.IDENTITY]
    for _ in range(radius):
        nxt = []
        for x in frontier:
            for s in gens:
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
    if order is None or order < 2:
        raise ValueError("h must have small finite order")
    powers = [h ** i for i in range(order)]
    base = ball(gens, r_m)
    M = {}
    for k in powers:
        for m in base.values():
            y = k * m
            M.setdefault(y.key, y)
    S = ball(gens, r_s)
    return h, order, powers, S, M


def relators(h, powers, S, M):
    """Index generators by element key; return (keys, relator list, h index).

    A relator is a pair (lhs, rhs) of generator-index lists (identity dropped)."""
    keys = sorted(set(S) | set(M), key=repr)
    ident = L.IDENTITY.key
    index = {k: i for i, k in enumerate(k for k in keys if k != ident)}

    def word(*ks):
        return [index[k] for k in ks if k != ident]

    rels = []
    by_product = {}
    for s_key, s in S.items():
        for m_key, m in M.items():
            by_product.setdefault((s * m).key, []).append((s_key, m_key))
    for pairs in by_product.values():
        s0, m0 = pairs[0]
        for s1, m1 in pairs[1:]:
            rels.append((word(s0, m0), word(s1, m1)))
    for k in powers[1:]:
        for m_key, m in M.items():
            rels.append((word(k.key, m_key), word((k * m).key)))
    return index, rels, index[h.key]


def rowspace_escape(rels, n, h_idx, p):
    """Return chi over F_p with chi . rel = 0 for all relators and chi[h] = 1, or None."""
    pivots = {}          # pivot column -> reduced row (dict col -> coeff)
    for lhs, rhs in rels:
        row = {}
        for c in lhs:
            row[c] = (row.get(c, 0) + 1) % p
        for c in rhs:
            row[c] = (row.get(c, 0) - 1) % p
        row = {c: v for c, v in row.items() if v}
        while row:
            c = min(row)
            if c in pivots:
                f = row[c]
                for cc, vv in pivots[c].items():
                    row[cc] = (row.get(cc, 0) - f * vv) % p
                row = {cc: vv for cc, vv in row.items() if vv}
            else:
                inv = pow(row[c], p - 2, p)
                pivots[c] = {cc: (vv * inv) % p for cc, vv in row.items()}
                break
    # full reduction so every pivot row is zero in the other pivot columns
    for c in sorted(pivots, reverse=True):
        for d in list(pivots):
            if d != c and c in pivots[d]:
                f = pivots[d][c]
                for cc, vv in pivots[c].items():
                    pivots[d][cc] = (pivots[d].get(cc, 0) - f * vv) % p
                pivots[d] = {cc: vv for cc, vv in pivots[d].items() if vv}
    # nullspace: free columns are non-pivots; chi[pivot] = -sum row[free] chi[free]
    free = [c for c in range(n) if c not in pivots]
    if h_idx in free:
        chi = [0] * n
        chi[h_idx] = 1
        for c, row in pivots.items():
            chi[c] = (-row.get(h_idx, 0)) % p
        return chi
    target = pivots[h_idx]
    for f in free:
        if target.get(f, 0):
            chi = [0] * n
            chi[f] = 1
            for c, row in pivots.items():
                chi[c] = (-row.get(f, 0)) % p
            return chi if chi[h_idx] % p else None
    return None


def check_chi(rels, chi, h_idx, p):
    for lhs, rhs in rels:
        if (sum(chi[c] for c in lhs) - sum(chi[c] for c in rhs)) % p:
            return False
    return chi[h_idx] % p != 0


def gap_file(path, n, rels, h_idx, max_index):
    names = ",".join('"x%d"' % i for i in range(n))

    def w(ix):
        return "*".join("F.%d" % (i + 1) for i in ix) if ix else "One(F)"
    rel_txt = ",\n".join("%s/(%s)" % (w(l), w(r)) for l, r in rels)
    with open(path, "w") as fh:
        fh.write("F := FreeGroup(%s);;\nrels := [%s];;\n" % (names, rel_txt))
        fh.write("U := F/rels;;\niso := IsomorphismSimplifiedFpGroup(U);;\nV := Range(iso);;\n")
        fh.write("yh := Image(iso, U.%d);;\nres := \"SURVIVES_TO_INDEX_%d\";;\n" % (h_idx + 1, max_index))
        fh.write("for K in LowIndexSubgroupsFpGroup(V, %d) do\n" % max_index)
        fh.write("  hom := FactorCosetAction(V, K);;\n  if Image(hom, yh) <> () then\n")
        fh.write("    res := Concatenation(\"SEP_INDEX_\", String(Index(V, K)));; break;\n  fi;\nod;\n")
        fh.write("Print(\"RESULT \", res, \" gens \", Length(GeneratorsOfGroup(V)), \"\\n\");\nQUIT;\n")


FAMILIES = [
    ("control-gl2", ["u", "v", "w"], "u"),
    ("v-plus-swap", ["w", "a", "A"], "w"),
    ("transvections-depth12", ["u", "v", "t", "q", "r"], "u"),
    ("transvections-swap", ["w", "t", "q", "r"], "w"),
    ("order3-thompson", ["g", "G", "a", "A"], "g"),
    ("order3-transvections", ["g", "G", "t", "q", "r"], "g"),
    ("mixed-all", ["u", "v", "w", "a", "A", "t", "q", "r"], "u"),
    ("mixed-all-order3", ["g", "G", "w", "a", "A", "t", "q", "r"], "g"),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    ap.add_argument("--gap-dir")
    ap.add_argument("--radii", default="1:1,1:2,2:1,2:2")
    ap.add_argument("--max-index", type=int, default=5)
    ap.add_argument("--verify")
    args = ap.parse_args()
    if args.verify:
        data = json.load(open(args.verify))
        units = named_units()
        bad = 0
        for rec in data:
            if rec["stage1"] != "separated":
                continue
            h, order, powers, S, M = window(units, rec["gens"], rec["h"], rec["r_m"], rec["r_s"])
            index, rels, h_idx = relators(h, powers, S, M)
            ok = check_chi(rels, rec["chi"], h_idx, rec["p"])
            bad += not ok
            print(rec["family"], rec["r_m"], rec["r_s"], "witness", "OK" if ok else "FAIL")
        sys.exit(1 if bad else 0)
    units = named_units()
    radii = [tuple(int(x) for x in rr.split(":")) for rr in args.radii.split(",")]
    results = []
    for (fam, gens, h_name), (r_m, r_s) in itertools.product(FAMILIES, radii):
        h, order, powers, S, M = window(units, gens, h_name, r_m, r_s)
        index, rels, h_idx = relators(h, powers, S, M)
        n = len(index)
        rec = {"family": fam, "gens": gens, "h": h_name, "order": order, "r_m": r_m, "r_s": r_s,
               "S": len(S), "M": len(M), "generators": n, "relators": len(rels)}
        p = order if order in (2, 3, 5, 7) else None
        chi = rowspace_escape(rels, n, h_idx, p) if p else None
        if chi is not None and check_chi(rels, chi, h_idx, p):
            rec.update(stage1="separated", p=p, chi=chi)
        else:
            rec.update(stage1="survives", p=p)
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
