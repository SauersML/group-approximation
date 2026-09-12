"""Rule-free screen of invariant-output windows over Thompson's group V.

Lane `gottschalk-thompson-v`, 2026-09-12. This adapts
experiments/gottschalk-small-presentations/window_table_screen.py, the screen over
the Leavitt unit group, to V itself. Exact tree-pair arithmetic replaces the Leavitt
checker.

Setting: research/strict-pairs-transfer-to-table-realizations.md, Corollary 3.
- A window is (S, M, H): H = <h> is finite cyclic, 1 lies in S and in M, and HM = M.
- Its table group U has a generator x_a for each a in S u M, with x_1 = 1, and relators

      x_s x_m = x_s' x_m'   whenever s m = s' m' in V   (s, s' in S; m, m' in M),
      x_k x_m = x_(k m)     for k in H, m in M.

- If some homomorphism from U into a finite group sends x_h to a nontrivial element,
  no pair of local rules on that window is strict, whatever the rules.

Elements:
- An element of V is a bijection between two complete prefix codes over {0,1}. It
  acts on {0,1}^N by a_i w -> b_i w.
- We store the reduced form: merge sibling pairs (c0 -> d0, c1 -> d1) into c -> d
  until none remain. The reduced form is unique, so two elements are equal iff their
  keys are equal.
- Products compose maps: (g * f)(w) = g(f(w)).

Stages:
1. Characters U -> Z/p (p = order of h, prime), by linear algebra over F_p.
2. For survivors, a GAP file: Tietze simplification, then small simple targets, then
   low-index coset actions.
Every witness is replayed by --verify.

MSI usage:
  python3 v_window_screen.py --selftest
  python3 v_window_screen.py --out results.json --gap-dir gap/
  sage -gap -q gap/<window>.g          # writes gap/<window>.witness.json
  python3 v_window_screen.py --verify results.json --gap-dir gap/
"""

import argparse
import itertools
import json
import os
import random
import sys


def is_complete_prefix_code(words):
    ws = sorted(words)
    if any(y.startswith(x) for x, y in zip(ws, ws[1:])):
        return False
    depth = max(len(w) for w in ws)
    return sum(1 << (depth - len(w)) for w in ws) == 1 << depth


def reduce_pairs(pairs):
    table = dict(pairs)
    changed = True
    while changed:
        changed = False
        for c in list(table):
            if not c or c[-1] != "0" or c not in table:
                continue
            sib = c[:-1] + "1"
            d0, d1 = table[c], table.get(sib)
            if d1 is None or not d0 or d0[-1] != "0" or d1 != d0[:-1] + "1":
                continue
            del table[c], table[sib]
            table[c[:-1]] = d0[:-1]
            changed = True
    return tuple(sorted(table.items()))


class V:
    __slots__ = ("key",)

    def __init__(self, pairs):
        self.key = reduce_pairs(pairs)

    @classmethod
    def from_codes(cls, domain, image):
        assert len(domain) == len(image)
        assert is_complete_prefix_code(domain) and is_complete_prefix_code(image)
        return cls(zip(domain, image))

    def __eq__(self, other):
        return self.key == other.key

    def __hash__(self):
        return hash(self.key)

    def __mul__(self, other):
        """(self * other)(w) = self(other(w))."""
        g = dict(self.key)
        out = []
        for a, b in other.key:
            for i in range(len(b) + 1):
                if b[:i] in g:
                    out.append((a, g[b[:i]] + b[i:]))
                    break
            else:
                out.extend((a + c[len(b):], d) for c, d in self.key if c.startswith(b))
        return V(out)

    def inverse(self):
        return V((b, a) for a, b in self.key)

    def __pow__(self, n):
        x = IDENTITY
        for _ in range(n):
            x = x * self
        return x

    def order(self, limit=60):
        x = self
        for n in range(1, limit + 1):
            if x.key == IDENTITY.key:
                return n
            x = x * self
        return None

    def act(self, word):
        """Image of a finite word at least as long as every domain leaf."""
        for a, b in self.key:
            if word.startswith(a):
                return b + word[len(a):]
        raise ValueError("word shorter than the domain code")


IDENTITY = V([("", "")])


def leaf_perm(code, perm):
    """The element sending the leaf code[i] to the leaf code[perm[i]]."""
    return V.from_codes(code, [code[j] for j in perm])


def named_elements():
    E = {}
    # Cannon--Floyd--Parry generators of F, T, V, as prefix replacements
    E["A"] = V.from_codes(["0", "10", "11"], ["00", "01", "1"])
    E["B"] = V.from_codes(["0", "10", "110", "111"], ["0", "100", "101", "11"])
    E["C"] = V.from_codes(["0", "10", "11"], ["11", "0", "10"])
    E["p0"] = V.from_codes(["0", "10", "11"], ["10", "0", "11"])
    E["p1"] = V.from_codes(["0", "10", "110", "111"], ["0", "110", "10", "111"])
    E["s"] = V.from_codes(["0", "1"], ["1", "0"])
    code4 = ["00", "01", "10", "11"]
    E["t4"] = leaf_perm(code4, [1, 0, 2, 3])
    E["c4"] = leaf_perm(code4, [1, 2, 3, 0])
    code5 = ["00", "010", "011", "10", "11"]
    E["c5"] = leaf_perm(code5, [1, 2, 3, 4, 0])
    E["c3"] = leaf_perm(code5, [1, 2, 0, 3, 4])
    E["d22"] = leaf_perm(code5, [1, 0, 3, 2, 4])
    # GL(3,2) on the eight depth-3 cylinders, read as vectors of F_2^3
    code8 = ["".join(bits) for bits in itertools.product("01", repeat=3)]

    def image(w, move):
        v = [int(ch) for ch in w]
        return code8.index("".join(map(str, move(v))))

    def transvection(i, j):
        def move(v):
            v = list(v)
            v[i] ^= v[j]
            return v
        return move

    for i, j in itertools.permutations(range(3), 2):
        E["e%d%d" % (i, j)] = leaf_perm(code8, [image(w, transvection(i, j)) for w in code8])
    E["r3"] = leaf_perm(code8, [image(w, lambda v: [v[2], v[0], v[1]]) for w in code8])
    return E


GL32 = ["e01", "e10", "e02", "e20", "e12", "e21"]
FAMILIES = {
    "t-cfp-order3": (["A", "B", "C"], "C"),
    "t-cfp-half-turn": (["A", "B", "s"], "s"),
    "f-plus-p0": (["A", "B", "p0"], "p0"),
    "v-cfp-order2": (["A", "B", "C", "p0"], "p0"),
    "v-cfp-order3": (["A", "B", "C", "p0"], "C"),
    "v-cfp-p1": (["A", "B", "C", "p0", "p1"], "p1"),
    "v-torsion-2-3": (["p0", "C"], "p0"),
    "v-torsion-2-3-order3": (["p0", "C"], "C"),
    "sym4-leaves-f": (["t4", "c4", "A", "B"], "t4"),
    "alt5-leaves-f-order3": (["c5", "c3", "A", "B"], "c3"),
    "alt5-leaves-f-order2": (["c5", "c3", "A", "B"], "d22"),
    "gl32-leaves-f-order2": (GL32 + ["A", "B"], "e01"),
    "gl32-leaves-f-order3": (GL32 + ["A", "B"], "r3"),
    "gl32-leaves-v-order2": (GL32 + ["p0", "C"], "e01"),
}


def ball(gens, radius):
    steps = []
    for x in gens:
        steps.append(x)
        if x.inverse().key != x.key:
            steps.append(x.inverse())
    elems = {IDENTITY.key: IDENTITY}
    frontier = [IDENTITY]
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


def window(E, gen_names, h_name, r_m, r_s):
    gens = [E[n] for n in gen_names]
    h = E[h_name]
    order = h.order(limit=12)
    powers = [h ** i for i in range(order)]
    base = ball(gens, r_m).values()
    M = {}
    for k in powers:
        for m in base:
            y = k * m
            M.setdefault(y.key, y)
    return h, order, powers, ball(gens, r_s), M


def relators(h, powers, S, M):
    keys = sorted(set(S) | set(M), key=repr)
    ident = IDENTITY.key
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
        fh.write("U := F/rels;;\niso := IsomorphismSimplifiedFpGroup(U);;\nW := Range(iso);;\n"
                 "yh := Image(iso, U.%d);;\nres := \"SURVIVES\";;\n" % (h_idx + 1))
        fh.write("Print(\"SIMPLIFIED gens \", Length(GeneratorsOfGroup(W)), \" rels \",\n"
                 "  Length(RelatorsOfFpGroup(W)), \"\\n\");\n")
        fh.write("record := function(hom, deg, tag)\n"
                 "  local imgs, ok, out;\n"
                 "  imgs := List(GeneratorsOfGroup(U), x -> Image(hom, Image(iso, x)));\n"
                 "  ok := ForAll(rels, rr -> MappedWord(rr, GeneratorsOfGroup(F), imgs) = ());\n"
                 "  out := OutputTextFile(\"%s\", false); SetPrintFormattingStatus(out, false);\n"
                 "  PrintTo(out, \"{\\\"index\\\": \", deg, \", \\\"gap_relators_ok\\\": \", ok,\n"
                 "    \", \\\"image\\\": \\\"\", tag, \"\\\", \\\"perms\\\": \",\n"
                 "    List(imgs, x -> ListPerm(x, deg)), \"}\\n\");\n"
                 "  CloseStream(out);\nend;;\n" % wit)
        fh.write("targets := [[AlternatingGroup(5), \"A5\"], [PSL(3,2), \"PSL(3,2)\"],\n"
                 "  [AlternatingGroup(6), \"A6\"], [AlternatingGroup(7), \"A7\"],\n"
                 "  [PSL(2,8), \"PSL(2,8)\"], [AlternatingGroup(8), \"A8\"], [PSL(2,11), \"PSL(2,11)\"]];;\n"
                 "for T in targets do\n"
                 "  if res = \"SURVIVES\" then\n"
                 "    for hom in GQuotients(W, T[1]) do\n"
                 "      if res = \"SURVIVES\" and Image(hom, yh) <> () then\n"
                 "        record(hom, LargestMovedPoint(T[1]), T[2]);\n"
                 "        res := Concatenation(\"SEP_QUOTIENT_\", T[2]);\n"
                 "      fi;\n    od;\n  fi;\nod;\n")
        fh.write("if res = \"SURVIVES\" then\n"
                 "  for K in LowIndexSubgroupsFpGroup(W, %d) do\n"
                 "    hom := FactorCosetAction(W, K);\n"
                 "    if res = \"SURVIVES\" and Image(hom, yh) <> () then\n"
                 "      record(hom, Index(W, K), \"cosets\");\n"
                 "      res := Concatenation(\"SEP_INDEX_\", String(Index(W, K)));\n"
                 "    fi;\n  od;\n"
                 "  if res = \"SURVIVES\" then res := \"SURVIVES_TARGETS_AND_INDEX_%d\"; fi;\n"
                 "fi;\nPrint(\"RESULT \", res, \"\\n\");\nQUIT;\n" % (max_index, max_index))


def selftest(seed=1):
    rng = random.Random(seed)
    E = named_elements()
    names = sorted(E)

    def rand_elt(k):
        x = IDENTITY
        for _ in range(k):
            y = E[rng.choice(names)]
            x = x * (y if rng.random() < 0.5 else y.inverse())
        return x
    for _ in range(300):
        f, g, h = rand_elt(4), rand_elt(4), rand_elt(4)
        assert (f * g) * h == f * (g * h)
        assert f * f.inverse() == IDENTITY and f.inverse() * f == IDENTITY
        assert is_complete_prefix_code([a for a, _ in f.key])
        assert is_complete_prefix_code([b for _, b in f.key])
        w = "".join(rng.choice("01") for _ in range(200))
        assert (f * g).act(w) == f.act(g.act(w))
    for _ in range(100):
        f = rand_elt(3)
        pairs = list(f.key)
        a, b = pairs.pop(rng.randrange(len(pairs)))
        pairs += [(a + "0", b + "0"), (a + "1", b + "1")]
        assert V(pairs) == f, "reduced form not canonical"
    orders = {"C": 3, "p0": 2, "p1": 2, "s": 2, "t4": 2, "c4": 4, "c5": 5, "c3": 3,
              "d22": 2, "e01": 2, "r3": 3}
    for name, n in orders.items():
        assert E[name].order() == n, name
    assert E["A"].order(limit=40) is None and E["B"].order(limit=40) is None
    A, B = E["A"], E["B"]
    Ai, Bi = A.inverse(), B.inverse()

    def comm(x, y):
        return x * y == y * x
    left = comm(A * Bi, Ai * B * A) and comm(A * Bi, Ai * Ai * B * A * A)
    right = comm(Bi * A, A * B * Ai) and comm(Bi * A, A * A * B * Ai * Ai)
    assert left or right, "CFP relators of F fail in both conventions"
    assert E["C"] ** 3 == IDENTITY and (E["p0"] * E["C"]) != (E["C"] * E["p0"])
    gl = ball([E[x] for x in GL32], 12)
    assert len(gl) == 168, len(gl)
    print("selftest OK (CFP convention: %s)" % ("left" if left else "right"), flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    ap.add_argument("--gap-dir")
    ap.add_argument("--families", default=",".join(FAMILIES))
    ap.add_argument("--radii", default="1:1,1:2,2:1,2:2")
    ap.add_argument("--max-index", type=int, default=6)
    ap.add_argument("--verify")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        selftest()
        return
    E = named_elements()
    if args.verify:
        bad = 0
        for rec in json.load(open(args.verify)):
            h, order, powers, S, M = window(E, rec["gens"], rec["h"], rec["r_m"], rec["r_s"])
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
                how = "permutation image of degree %d (%s)" % (wit["index"], wit.get("image", "?"))
            bad += not ok
            print(tag, how, "OK" if ok else "FAIL")
        print("VERIFY_DONE bad=%d" % bad)
        sys.exit(1 if bad else 0)
    radii = [tuple(int(x) for x in rr.split(":")) for rr in args.radii.split(",")]
    results = []
    for fam, (r_m, r_s) in itertools.product(args.families.split(","), radii):
        gens, h_name = FAMILIES[fam]
        h, order, powers, S, M = window(E, gens, h_name, r_m, r_s)
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
    print("SCREEN_DONE windows=%d survivors=%d" % (
        len(results), sum(r["stage1"] == "survives" for r in results)), flush=True)


if __name__ == "__main__":
    main()
