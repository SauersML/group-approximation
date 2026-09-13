#!/usr/bin/env python3
"""Independent checks on the completeness proofs of two presentations of L_(F_2)(1,2)^x.

Lane ex-verify-presentation, 2026-09-12.  Objects under review: the sixty-relator group P of
leavitt-unit-group-steinberg-weyl-presentation and the eighteen-relator group Q of
thompson-steinberg-presentation-of-leavitt-unit-group.  No computation can prove completeness.
These checks rebuild the inputs without reusing the authoring lane's scripts:

  A. an own Todd-Coxeter enumeration of <c, t | W>, with a (2,3,5) triangle group control;
  B. the literal JSON relator words, evaluated under images built here.  Bleak--Quick's b is
     built as t_(01,10) t_(01,11) under their right action, not chosen between two 3-cycles;
  C. Bleak--Quick (2.4) transcribed from the TeX and compared with the JSON (V) block, and (2.3)
     evaluated;
  D. abelianizations of P and Q, by integer elimination;
  E. identities used in the completeness proofs, evaluated in L^x.
"""
import hashlib
import itertools
import json
import os
import random
import re
import sys
import time

sys.path.insert(0, os.environ["CERT_DIR"])
import leavitt as Lv  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
LETTERS = {"1": ("", ""), "e": ("0", ""), "f": ("1", ""), "E": ("", "0"), "F": ("", "1")}
LETTER_ELEM = {"1": Lv.ONE, "e": Lv.s0, "f": Lv.s1, "E": Lv.t0, "F": Lv.t1}
D = ["00", "01", "10", "110", "111"]


def tv(al, be):
    return Lv.one_plus_nilpotent(Lv.S(al) * Lv.T(be))


def comm(p, q):
    return p * q * p.inverse() * q.inverse()


def inv(w):
    return [(g, -e) for g, e in reversed(w)]


def reduce(w):
    out = []
    for g, e in w:
        if out and out[-1] == (g, -e):
            out.pop()
        else:
            out.append((g, e))
    return out


def render(w):
    return " ".join(g if e == 1 else g + "^-1" for g, e in w)


def parse_literal(word):
    return [(tok[:-3], -1) if tok.endswith("^-1") else (tok, 1) for tok in word.split()]


def evaluate(w, units):
    u = Lv.IDENTITY
    for g, e in w:
        u = u * (units[g] if e == 1 else units[g].inverse())
    return u


def parse_tex(text):
    """Letters, (W)^{n}, X^{W} = W^-1 X W, [X,Y] = X^-1 Y^-1 X Y (Bleak--Quick conventions)."""
    s = text.replace(" ", "")
    pos = [0]

    def seq(stops):
        w = []
        while pos[0] < len(s) and s[pos[0]] not in stops:
            w += item()
        return w

    def item():
        ch = s[pos[0]]
        if ch == "(":
            pos[0] += 1
            w = seq(")")
            pos[0] += 1
        elif ch == "[":
            pos[0] += 1
            x = seq(",")
            pos[0] += 1
            y = seq("]")
            pos[0] += 1
            w = inv(x) + inv(y) + x + y
        else:
            assert ch.isalpha(), (text, pos[0])
            w = [(ch, 1)]
            pos[0] += 1
        while pos[0] < len(s) and s[pos[0]] == "^":
            pos[0] += 2
            m = re.match(r"-?\d+\}", s[pos[0]:])
            if m:
                n = int(m.group(0)[:-1])
                pos[0] += len(m.group(0))
                w = w * n if n >= 0 else inv(w) * (-n)
            else:
                y = seq("}")
                pos[0] += 1
                w = inv(y) + w + y
        return w

    w = seq("")
    assert pos[0] == len(s), text
    return reduce(w)


BQ_23 = ["a^{2}", "b^{3}", "(ab)^{4}", "c^{-1}a^{bcacaa^{ba}}a^{b^{-1}cacaa^{b^{-1}a}}",
         "[a^{b^{-1}cac},a^{b^{-1}caca^{b}a^{b^{-1}a}}]", "c^{ac}a^{-1}",
         "[a^{bcac},a^{b^{-1}caca^{b}a^{b^{-1}a}}]", "[a^{bca^{bca}},a^{bcaca^{b}a^{b^{-1}a}}]"]
BQ_24 = ["a^{2}", "b^{3}", "(ab)^{4}", "c^{-1}(ac)^{2}a", "(cab^{-1}aba)^{2}cb(cabab^{-1}a)^{2}",
         "a(cb)^{2}a(b^{-1}c)^{2}bcabcb^{-1}cab^{-1}acb^{-1}(cb)^{2}ab^{-1}",
         "ab^{-1}cbc(ab^{-1})^{2}cbcb^{-1}a(b^{-1}c)^{2}babcb^{-1}cab^{-1}",
         "ca(b^{-1}c)^{2}bacabacbc(b^{-1}ca)^{2}b(cb^{-1})^{2}(acb)^{2}cb^{-1}cab^{-1}"]


def todd_coxeter(ngens, rels, limit=50000):
    """HLT enumeration over the trivial subgroup; generator x has inverse x ^ 1."""
    table = [[None] * (2 * ngens)]
    parent = [0]

    def rep(k):
        root = k
        while parent[root] != root:
            root = parent[root]
        while parent[k] != root:
            parent[k], k = root, parent[k]
        return root

    def define(cos, x):
        if len(table) >= limit:
            raise RuntimeError("coset limit")
        table.append([None] * (2 * ngens))
        parent.append(len(table) - 1)
        table[cos][x] = len(table) - 1
        table[-1][x ^ 1] = cos

    def merge(k, l, queue):
        k, l = rep(k), rep(l)
        if k != l:
            k, l = min(k, l), max(k, l)
            parent[l] = k
            queue.append(l)

    def coincidence(a, b):
        queue = []
        merge(a, b, queue)
        i = 0
        while i < len(queue):
            e = queue[i]
            i += 1
            for x in range(2 * ngens):
                f = table[e][x]
                if f is None:
                    continue
                table[f][x ^ 1] = None
                e1, f1 = rep(e), rep(f)
                if table[e1][x] is not None:
                    merge(f1, table[e1][x], queue)
                elif table[f1][x ^ 1] is not None:
                    merge(e1, table[f1][x ^ 1], queue)
                else:
                    table[e1][x], table[f1][x ^ 1] = f1, e1

    def scan_and_fill(cos, w):
        f, b, i, j = cos, cos, 0, len(w) - 1
        while True:
            while i <= j and table[f][w[i]] is not None:
                f, i = table[f][w[i]], i + 1
            if i > j:
                if f != b:
                    coincidence(f, b)
                return
            while j >= i and table[b][w[j] ^ 1] is not None:
                b, j = table[b][w[j] ^ 1], j - 1
            if j < i:
                coincidence(f, b)
                return
            if i == j:
                table[f][w[i]], table[b][w[i] ^ 1] = b, f
                return
            define(f, w[i])

    cos = 0
    while cos < len(table):
        for w in rels:
            if parent[cos] != cos:
                break
            scan_and_fill(cos, w)
        for x in range(2 * ngens):
            if parent[cos] == cos and table[cos][x] is None:
                define(cos, x)
        cos += 1
    live = [k for k in range(len(table)) if parent[k] == k]
    idx = {k: n for n, k in enumerate(live)}
    perm = [[idx[rep(table[k][x])] for x in range(2 * ngens)] for k in live]
    ok = all(sorted(perm[k][x] for k in range(len(live))) == list(range(len(live))) for x in range(2 * ngens))
    ok = ok and all(perm[perm[k][x]][x ^ 1] == k for k in range(len(live)) for x in range(2 * ngens))
    for k in range(len(live)):
        for w in rels:
            q = k
            for x in w:
                q = perm[q][x]
            ok = ok and q == k
    return len(live), ok


def lattice_diagonal(rows, n):
    """Diagonal of a triangular basis of the row lattice; abelianization is trivial iff all are 1."""
    rows = [list(r) for r in rows if any(r)]
    diag = []
    for col in range(n):
        while len([r for r in rows if r[col]]) > 1:
            nz = sorted([r for r in rows if r[col]], key=lambda r: abs(r[col]))
            for r in nz[1:]:
                q = r[col] // nz[0][col]
                for k in range(n):
                    r[k] -= q * nz[0][k]
        nz = [r for r in rows if r[col]]
        if not nz:
            diag.append(0)
            continue
        rows.remove(nz[0])
        diag.append(abs(nz[0][col]))
    return diag


def exponent_rows(relators, gens):
    return [[sum(e for g, e in parse_literal(r["word"]) if g == name) for name in gens] for r in relators]


def swap(al, be):
    def rec(p):
        if p in (al, be) or not any(c.startswith(p) for c in (al, be)):
            return [p]
        return rec(p + "0") + rec(p + "1")
    code = rec("")
    return Lv.thompson_unit(code, [be if d == al else al if d == be else d for d in code])


def theta_perm(p):
    return Lv.thompson_unit(D, [D[p[j] - 1] for j in range(5)])


def random_code(rng, size):
    code = [""]
    while len(code) < size:
        leaf = rng.choice(code)
        if len(leaf) < 5:
            code.remove(leaf)
            code += [leaf + "0", leaf + "1"]
    return code


def main():
    t0 = time.time()
    out = {}
    rng = random.Random(20260912)
    # A. Weyl block
    W = [[2, 2], [0] * 5, [2, 0] * 4, [2, 1, 2, 0] * 3, [2, 1, 1, 2, 0, 0] * 2]
    out["A_weyl_cosets"] = todd_coxeter(2, W)
    out["A_control_235_cosets"] = todd_coxeter(2, [[0, 0], [2] * 3, [0, 2] * 5])
    # B. literal relators under images built here
    Lv.set_dual(True)
    data = {k: json.load(open(os.path.join(HERE, f))) for k, f in
            [("P", "st5-weyl-presentation.json"), ("Q", "thompson-steinberg-presentation.json")]}
    unitsP = {"c": theta_perm((2, 3, 4, 5, 1)), "t": theta_perm((2, 1, 3, 4, 5))}
    for name, (ls, lt) in LETTERS.items():
        unitsP["y" + name] = tv("00" + ls, "01" + lt)
    b_bq = swap("01", "10") * swap("01", "11")
    unitsQ = {"a": swap("00", "01"), "b": b_bq, "c": swap("1", "00"), "x": tv("00", "01")}
    out["B_b_equals_lane_reading"] = b_bq == Lv.thompson_unit(["00", "01", "10", "11"], ["00", "11", "01", "10"])
    for k, units in (("P", unitsP), ("Q", unitsQ)):
        rels = data[k]["relators"]
        words = [r["word"] for r in rels]
        out["B_%s" % k] = {
            "count": len(rels), "failing": [r["name"] for r in rels if not evaluate(parse_literal(r["word"]), units).is_identity()],
            "total_length": sum(len(parse_literal(w)) for w in words), "max_length": max(len(parse_literal(w)) for w in words),
            "sha_matches_json": hashlib.sha256("\n".join(words).encode()).hexdigest() == data[k]["relator_sha256"]}
    # C. Bleak--Quick transcription
    vjson = [r["word"] for r in data["Q"]["relators"] if r["family"] == "V"]
    out["C_24_tex_equals_json"] = [render(parse_tex(r)) == w for r, w in zip(BQ_24, vjson)]
    out["C_23_hold"] = [evaluate(parse_tex(r), unitsQ).is_identity() for r in BQ_23]
    conj = data["Q"]["conjugators"]
    iota = {"iota1(a)": ("a", swap("100", "101")), "iota1(b)": ("b", swap("101", "110") * swap("101", "111")),
            "iota1(c)": ("a", swap("11", "100"))}
    out["C_iota_images"] = {k: evaluate(reduce(parse_literal(conj[k]) + [(g, 1)] + inv(parse_literal(conj[k]))), unitsQ) == u
                            for k, (g, u) in iota.items()}
    out["C_T_images"] = {k: evaluate(reduce(parse_literal(conj[k]) + [("x", 1)] + inv(parse_literal(conj[k]))), unitsQ)
                         == tv(*k[2:-1].split(",")) for k in conj if k.startswith("T(")}
    # D. abelianizations
    out["D_abelianization_diagonal_P"] = lattice_diagonal(exponent_rows(data["P"]["relators"], ["c", "t", "y1", "ye", "yf", "yE", "yF"]), 7)
    out["D_abelianization_diagonal_Q"] = lattice_diagonal(exponent_rows(data["Q"]["relators"], ["a", "b", "c", "x"]), 4)
    Lv.set_dual(False)
    # E1. the sixty-relator proof, through words in c, t
    words = {(1, 2, 3, 4, 5): Lv.IDENTITY}
    frontier = [(1, 2, 3, 4, 5)]
    gens = [((2, 3, 4, 5, 1), unitsP["c"]), ((5, 1, 2, 3, 4), unitsP["c"].inverse()), ((2, 1, 3, 4, 5), unitsP["t"])]
    while frontier:
        nxt = []
        for p in frontier:
            for g, u in gens:
                q = tuple(p[g[j] - 1] for j in range(5))
                if q not in words:
                    words[q] = words[p] * u
                    nxt.append(q)
        frontier = nxt
    collections_count = 0
    bad = []
    out["E1_weyl_words"] = len(words)
    bad += [p for p, u in words.items() if u != theta_perm(p)]
    X = {}
    for p, u in words.items():
        for a in LETTERS:
            val = u * unitsP["y" + a] * u.inverse()
            key = (p[0], p[1], a)
            if val != tv(D[p[0] - 1] + LETTERS[a][0], D[p[1] - 1] + LETTERS[a][1]):
                bad.append(("conj", p, a))
            X.setdefault(key, val)
    roots = [(i, j) for i in range(1, 6) for j in range(1, 6) if i != j]
    for (i, j), (k, l) in itertools.product(roots, repeat=2):
        if j != k and l != i:
            for a, b in itertools.product(LETTERS, repeat=2):
                collections_count += 1
                if not comm(X[i, j, a], X[k, l, b]).is_identity():
                    bad.append(("B'", i, j, k, l, a, b))
    for i, j, m in itertools.permutations(range(1, 6), 3):
        for a in LETTERS:
            ok = X[i, j, a] == comm(X[i, m, "1"], X[m, j, a]) == comm(X[i, m, a], X[m, j, "1"])
            ok = ok and (X[i, j, a] * X[i, j, a]).is_identity()
            if not ok:
                bad.append(("unit split / square", i, j, m, a))
        for a, b in itertools.product(LETTERS, repeat=2):
            rhs = Lv.one_plus_nilpotent(Lv.S(D[i - 1]) * LETTER_ELEM[a] * LETTER_ELEM[b] * Lv.T(D[m - 1]))
            if comm(X[i, j, a], X[j, m, b]) != rhs:
                bad.append(("St3", i, j, m, a, b))
        if comm(X[i, j, "e"], X[j, m, "E"]) * comm(X[i, j, "f"], X[j, m, "F"]) != X[i, m, "1"]:
            bad.append(("partition", i, j, m))
    for i, j in roots:
        tr = [1, 2, 3, 4, 5]
        tr[i - 1], tr[j - 1] = j, i
        if X[i, j, "1"] * X[j, i, "1"] * X[i, j, "1"] != words[tuple(tr)]:
            bad.append(("weyl link", i, j))
    cyc = words[(2, 1, 3, 4, 5)] * words[(1, 3, 2, 4, 5)] * words[(1, 2, 4, 3, 5)] * words[(1, 2, 3, 5, 4)]
    out["E1_c_is_product_of_transpositions"] = cyc == unitsP["c"]
    out["E1_commutation_instances"] = collections_count
    out["E1_failures"] = [str(x) for x in bad]
    # E2. the eighteen-relator proof, on random cones
    bad = []
    trials = 0
    for _ in range(300):
        code = random_code(rng, rng.randint(5, 9))
        al, be, ga, de = rng.sample(code, 4)
        d = rng.choice("01")
        trials += 1
        checks = {
            "B-dis": comm(tv(al, be), tv(ga, de)).is_identity(), "B-src": comm(tv(al, be), tv(al, ga)).is_identity(),
            "B-tgt": comm(tv(al, ga), tv(be, ga)).is_identity(), "C11": comm(tv(al, be), tv(be, ga)) == tv(al, ga),
            "Q": tv(al + "0", be + "0") * tv(al + "1", be + "1") == tv(al, be), "X1": (tv(al, be) * tv(al, be)).is_identity(),
            "C1d": comm(tv(al, be), tv(be + d, ga)) == tv(al + d, ga), "CEd": comm(tv(al, be + d), tv(be, ga)) == tv(al, ga + d),
            "C1d-conjugation": comm(tv(al + "0", be + "0"), tv(al + "1", ga)).is_identity()}
        code2 = random_code(rng, len(code))
        rng.shuffle(code2)
        v = Lv.thompson_unit(code, code2)
        i, j = rng.sample(range(len(code)), 2)
        w1, w2 = "".join(rng.choice("01") for _ in range(rng.randint(0, 3))), "".join(rng.choice("01") for _ in range(rng.randint(0, 3)))
        checks["transport"] = v * tv(code[i] + w1, code[j] + w2) * v.inverse() == tv(code2[i] + w1, code2[j] + w2)
        i, j, k = rng.sample(range(5), 3)
        g1, dl = "".join(rng.choice("01") for _ in range(rng.randint(0, 3))), "".join(rng.choice("01") for _ in range(rng.randint(0, 3)))
        checks["suffix-source"] = tv(D[i] + g1 + d, D[j] + dl) == comm(tv(D[i] + g1, D[k]), tv(D[k] + d, D[j] + dl))
        checks["suffix-target"] = tv(D[i] + g1, D[j] + dl + d) == comm(tv(D[i] + g1, D[k] + d), tv(D[k], D[j] + dl))
        checks["same-leaf"] = tv(D[i] + "0" + g1, D[i] + "1" + dl) == comm(tv(D[i] + "0" + g1, D[k]), tv(D[k], D[i] + "1" + dl))
        bad += [(name, al, be, ga, de, d) for name, ok in checks.items() if not ok]
    out["E2_boundary_empty_complement_B-dis"] = comm(tv("00", "01"), tv("10", "11")).is_identity()
    out["E2_P_family_letters"] = all(
        comm(tv(D[0] + LETTERS[l][0], D[1] + LETTERS[l][1]), tv(D[1] + LETTERS[m][0], D[2] + LETTERS[m][1]))
        == comm(tv(D[0] + LETTERS[l][0], D[3] + LETTERS[l][1]), tv(D[3] + LETTERS[m][0], D[2] + LETTERS[m][1]))
        == Lv.one_plus_nilpotent(Lv.S(D[0]) * LETTER_ELEM[l] * LETTER_ELEM[m] * Lv.T(D[2]))
        for l, m in itertools.product(LETTERS, repeat=2))
    out["E2_random_trials"] = trials
    out["E2_failures"] = [str(x) for x in bad]
    out["seconds"] = round(time.time() - t0, 1)
    ok = tuple(out["A_weyl_cosets"]) == (120, True)
    ok = ok and tuple(out["A_control_235_cosets"]) == (60, True) and out["B_b_equals_lane_reading"]
    ok = ok and not out["B_P"]["failing"] and not out["B_Q"]["failing"] and out["B_P"]["sha_matches_json"] and out["B_Q"]["sha_matches_json"]
    ok = ok and all(out["C_24_tex_equals_json"]) and all(out["C_23_hold"]) and all(out["C_iota_images"].values())
    ok = ok and all(out["C_T_images"].values()) and set(out["D_abelianization_diagonal_P"]) == {1}
    ok = ok and set(out["D_abelianization_diagonal_Q"]) == {1}
    ok = ok and out["E1_weyl_words"] == 120 and out["E1_c_is_product_of_transpositions"] and not out["E1_failures"]
    ok = ok and out["E2_boundary_empty_complement_B-dis"] and out["E2_P_family_letters"] and not out["E2_failures"]
    out["verdict"] = "PASS" if ok else "FAIL"
    with open(os.environ.get("OUT_JSON", os.path.join(HERE, "review-presentation-consequences.json")), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out, indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
