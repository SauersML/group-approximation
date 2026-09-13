#!/usr/bin/env python3
"""Thompson's group V plus one leaf transvection presents the binary Leavitt unit group.

Generators a, b, c of V (Bleak--Quick, arXiv:1511.02123, Theorem 2.1: a = (00 01), b = (01 10 11),
c = (1 00), maps written on the right) and x = 1 + S[00]T[01] in L = L_{F_2}(1,2).
Images in L^x: a right-acting map g goes to psi(g) = U_g^-1, where U_g e_w = e_(w.g).  This is a
homomorphism.  For cones (alpha, beta), T(alpha, beta) := g x g^-1 with g a word whose unit
satisfies g S[00] = S[alpha] and g S[01] = S[beta].

Checks: the V relators ((2.3) and the shortened (2.4)) hold; BFS finds conjugator words and each
predicate is re-checked exactly; all relators of the presentation hold (dual mode); negative controls.
"""
import collections
import hashlib
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get("CERT_DIR", os.path.dirname(HERE)))
import leavitt as Lv  # noqa: E402

R_WORDS = [  # Bleak--Quick (2.3), Theorem 2.1, verbatim
    "a^{2}", "b^{3}", "(ab)^{4}", "c^{ac}a^{-1}",
    "c^{-1}a^{bcacaa^{ba}}a^{b^{-1}cacaa^{b^{-1}a}}",
    "[a^{b^{-1}cac},a^{b^{-1}caca^{b}a^{b^{-1}a}}]",
    "[a^{bcac},a^{b^{-1}caca^{b}a^{b^{-1}a}}]",
    "[a^{bca^{bca}},a^{bcaca^{b}a^{b^{-1}a}}]",
]
KB_WORDS = [  # Bleak--Quick (2.4), same normal closure as (2.3), verbatim
    "a^{2}", "b^{3}", "(ab)^{4}", "c^{-1}(ac)^{2}a",
    "(cab^{-1}aba)^{2}cb(cabab^{-1}a)^{2}",
    "a(cb)^{2}a(b^{-1}c)^{2}bcabcb^{-1}cab^{-1}acb^{-1}(cb)^{2}ab^{-1}",
    "ab^{-1}cbc(ab^{-1})^{2}cbcb^{-1}a(b^{-1}c)^{2}babcb^{-1}cab^{-1}",
    "ca(b^{-1}c)^{2}bacabacbc(b^{-1}ca)^{2}b(cb^{-1})^{2}(acb)^{2}cb^{-1}cab^{-1}",
]


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


def comm(x, y):
    return reduce(x + y + inv(x) + inv(y))


def render(w):
    return " ".join(g if e == 1 else g + "^-1" for g, e in w) or "1"


def parse_tex(text):
    """Letters, (..)^{n}, [X,Y] (= X^-1 Y^-1 X Y), X^{n} powers, X^{W} = W^-1 X W conjugates."""
    s = text.replace(" ", "")
    pos = [0]

    def peek():
        return s[pos[0]] if pos[0] < len(s) else ""

    def take(ch):
        assert peek() == ch, (text, pos[0], ch)
        pos[0] += 1

    def seq(stops):
        out = []
        while peek() and peek() not in stops:
            out += item()
        return out

    def item():
        if peek() == "(":
            take("(")
            w = seq(")")
            take(")")
        elif peek() == "[":
            take("[")
            x = seq(",")
            take(",")
            y = seq("]")
            take("]")
            w = inv(x) + inv(y) + x + y
        else:
            assert peek().isalpha(), (text, pos[0])
            w = [(peek(), 1)]
            pos[0] += 1
        while peek() == "^":
            take("^")
            take("{")
            m = re.match(r"-?\d+\}", s[pos[0]:])
            if m:
                n = int(m.group(0)[:-1])
                pos[0] += len(m.group(0))
                w = w * n if n >= 0 else inv(w) * (-n)
            else:
                y = seq("}")
                take("}")
                w = inv(y) + w + y
        return w

    w = seq("")
    assert pos[0] == len(s), text
    return reduce(w)


def complete_code(cones):
    def rec(p):
        if p in cones:
            return [p]
        if any(c.startswith(p) and c != p for c in cones):
            return rec(p + "0") + rec(p + "1")
        return [p]
    return rec("")


def cycle_unit(cycles):
    """U with U e_(a_i w) = e_(a_(i+1) w) for each cycle of disjoint cones, identity elsewhere."""
    cones = [x for cyc in cycles for x in cyc]
    image = {}
    for cyc in cycles:
        for i, x in enumerate(cyc):
            image[x] = cyc[(i + 1) % len(cyc)]
    code = complete_code(set(cones))
    return Lv.thompson_unit(code, [image.get(d, d) for d in code])


def transvection(alpha, beta):
    return Lv.one_plus_nilpotent(Lv.S(alpha) * Lv.T(beta))


def evaluate(w, units):
    u = Lv.IDENTITY
    for g, e in w:
        u = u * (units[g] if e == 1 else units[g].inverse())
    return u


def maps_cones(unit, pairs):
    return all(unit.val * Lv.S(src) == Lv.S(dst) for src, dst in pairs)


def bfs(units, targets, max_depth, cap):
    """Shortest words in a, b, b^-1, c with units meeting each predicate (a, c are involutions)."""
    steps = [("a", 1), ("b", 1), ("b", -1), ("c", 1)]
    found = {}
    frontier = [([], Lv.IDENTITY)]
    seen = {Lv.IDENTITY.key}
    for depth in range(max_depth + 1):
        for w, u in frontier:
            for name, pred in targets.items():
                if name not in found and pred(u):
                    found[name] = w
        if len(found) == len(targets) or depth == max_depth:
            break
        nxt = []
        for w, u in frontier:
            for st in steps:
                v = u * (units[st[0]] if st[1] == 1 else units[st[0]].inverse())
                if v.key not in seen and len(seen) < cap:
                    seen.add(v.key)
                    nxt.append((w + [st], v))
        frontier = nxt
    return found, len(seen)


def main():
    t0 = time.time()
    out = {}
    base = {"a": cycle_unit([["00", "01"]]), "c": cycle_unit([["1", "00"]]), "x": transvection("00", "01")}
    readings = {"b = inverse of U_(01 10 11)": cycle_unit([["11", "10", "01"]]),
                "b = U_(01 10 11)": cycle_unit([["01", "10", "11"]])}
    Lv.set_dual(True)
    chosen = None
    out["v_relator_check"] = {}
    for label, bu in readings.items():
        units = dict(base, b=bu)
        r_ok = [evaluate(parse_tex(r), units).is_identity() for r in R_WORDS]
        k_ok = [evaluate(parse_tex(r), units).is_identity() for r in KB_WORDS]
        out["v_relator_check"][label] = {"(2.3)": r_ok, "(2.4)": k_ok}
        if all(r_ok) and all(k_ok) and chosen is None:
            chosen = label
    out["b_reading"] = chosen
    if chosen is None:
        print(json.dumps(out, indent=1))
        return 1
    units = dict(base, b=readings[chosen])
    Lv.set_dual(False)
    targets = {
        "T(10,110)": lambda u: maps_cones(u, [("00", "10"), ("01", "110")]),
        "T(00,10)": lambda u: maps_cones(u, [("00", "00"), ("01", "10")]),
        "T(10,01)": lambda u: maps_cones(u, [("00", "10"), ("01", "01")]),
        "T(01,10)": lambda u: maps_cones(u, [("00", "01"), ("01", "10")]),
        "T(000,010)": lambda u: maps_cones(u, [("00", "000"), ("01", "010")]),
        "T(001,011)": lambda u: maps_cones(u, [("00", "001"), ("01", "011")]),
        "iota1(a)": lambda u: maps_cones(u, [("00", "100"), ("01", "101")]),
        "iota1(b)": lambda u: maps_cones(u, [("01", "101"), ("10", "110"), ("11", "111")]),
        "iota1(c)": lambda u: maps_cones(u, [("00", "11"), ("01", "100")]),
    }
    found, explored = bfs(units, targets, int(os.environ.get("BFS_DEPTH", "9")), int(os.environ.get("BFS_CAP", "400000")))
    out["bfs_explored"] = explored
    out["conjugators"] = {k: render(w) for k, w in found.items()}
    missing = sorted(set(targets) - set(found))
    out["conjugators_missing"] = missing
    if missing:
        print(json.dumps(out, indent=1))
        return 1
    Lv.set_dual(True)
    out["conjugator_predicates_rechecked"] = all(targets[k](evaluate(w, units)) for k, w in found.items())
    X = [("x", 1)]

    def T(name):
        g = found[name]
        return reduce(g + X + inv(g))

    def conj(name, letter):
        g = found[name]
        return reduce(g + [(letter, 1)] + inv(g))

    iota_b_expect = (cycle_unit([["111", "110", "101"]]) if chosen.startswith("b = inverse")
                     else cycle_unit([["101", "110", "111"]]))
    out["iota_images_exact"] = {
        "iota1(a) = (100 101)": evaluate(conj("iota1(a)", "a"), units) == cycle_unit([["100", "101"]]),
        "iota1(c) = (11 100)": evaluate(conj("iota1(c)", "a"), units) == cycle_unit([["11", "100"]]),
        "iota1(b) = (101 110 111)": evaluate(conj("iota1(b)", "b"), units) == iota_b_expect,
    }
    rels = []
    for i, r in enumerate(KB_WORDS, 1):
        rels.append(("V", "Bleak-Quick (2.4) r%d" % i, parse_tex(r)))
    rels.append(("X", "x^2", X * 2))
    rels.append(("X", "(a x)^3", ([("a", 1)] + X) * 3))
    rels.append(("H", "[x, iota1(a)]", comm(X, conj("iota1(a)", "a"))))
    rels.append(("H", "[x, iota1(b)]", comm(X, conj("iota1(b)", "b"))))
    rels.append(("H", "[x, iota1(c)]", comm(X, conj("iota1(c)", "a"))))
    rels.append(("B", "[T(00,01), T(10,110)]  disjoint", comm(X, T("T(10,110)"))))
    rels.append(("B", "[T(00,01), T(00,10)]  same source", comm(X, T("T(00,10)"))))
    rels.append(("B", "[T(00,01), T(10,01)]  same target", comm(X, T("T(10,01)"))))
    rels.append(("C", "[T(00,01), T(01,10)] = T(00,10)", reduce(comm(X, T("T(01,10)")) + inv(T("T(00,10)")))))
    rels.append(("Q", "T(000,010) T(001,011) = T(00,01)", reduce(T("T(000,010)") + T("T(001,011)") + inv(X))))
    fails = [n for f, n, w in rels if not evaluate(w, units).is_identity()]
    out["relator_count"] = len(rels)
    out["generator_count"] = 4
    out["relators_failing_in_G"] = fails
    out["total_length"] = sum(len(w) for _f, _n, w in rels)
    out["max_length"] = max(len(w) for _f, _n, w in rels)
    out["x_relator_total_length"] = sum(len(w) for f, _n, w in rels if f != "V")
    out["relators"] = [{"family": f, "name": n, "word": render(w), "length": len(w)} for f, n, w in rels]
    out["relator_sha256"] = hashlib.sha256("\n".join(render(w) for _f, _n, w in rels).encode()).hexdigest()
    exact = {"T(%s)" % k[2:-1]: transvection(*k[2:-1].split(",")) for k in targets if k.startswith("T(")}
    out["transvection_images_exact"] = {k: evaluate(T(k), units) == v for k, v in exact.items()}
    neg = {
        "(b x)^3 = 1": ([("b", 1)] + X) * 3,
        "T(000,010) = T(00,01)  (half a split)": reduce(T("T(000,010)") + inv(X)),
        "[T(00,01), T(01,10)] = T(10,110)": reduce(comm(X, T("T(01,10)")) + inv(T("T(10,110)"))),
        "[x, a] = 1": comm(X, [("a", 1)]),
        "[x, T(01,10)] = 1": comm(X, T("T(01,10)")),
    }
    out["negative_controls_nonidentity"] = {k: not evaluate(w, units).is_identity() for k, w in neg.items()}
    out["dual"] = Lv.dual_stats()
    out["seconds"] = round(time.time() - t0, 1)
    ok = (not fails and out["conjugator_predicates_rechecked"] and all(out["iota_images_exact"].values())
          and all(out["transvection_images_exact"].values()) and all(out["negative_controls_nonidentity"].values()))
    out["verdict"] = "PASS" if ok else "FAIL"
    with open(os.environ.get("OUT_JSON", os.path.join(HERE, "thompson-steinberg-presentation.json")), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "relators"}, indent=1))
    for f, n, w in rels:
        print("%s | %-40s | %3d | %s" % (f, n, len(w), render(w)))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
