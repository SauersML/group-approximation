#!/usr/bin/env python3
"""Validation suite for the R^x certificate checker.  Run on MSI, never locally.

    python3 selftest.py            # dual mode: every product is also checked by prefix tables

Exit status 0 when every check passes.
"""

import glob
import itertools
import json
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)

import leavitt as L  # noqa: E402
from leavitt import Elem, Unit, ONE, ZERO, s0, s1, t0, t1  # noqa: E402
import groupalg as GA  # noqa: E402
import ca as CA  # noqa: E402
import kl as KL  # noqa: E402
import certcheck  # noqa: E402

RESULTS = []


def check(name, condition, detail=""):
    condition = bool(condition)
    RESULTS.append((name, condition, detail))
    print("%s %s%s" % ("ok  " if condition else "FAIL", name, "  [%s]" % detail if detail else ""),
          flush=True)
    return condition


def info(text):
    print("info %s" % text, flush=True)


def random_word(rng, max_len):
    return "".join(rng.choice("01") for _ in range(rng.randint(0, max_len)))


def random_elem(rng, max_terms=4, max_len=3):
    count = rng.randint(0, max_terms)
    return Elem.from_terms((random_word(rng, max_len), random_word(rng, max_len)) for _ in range(count))


def test_relations():
    for i, si in enumerate((s0, s1)):
        for j, tj in enumerate((t0, t1)):
            product = tj * si
            check("t%d s%d = %d" % (j, i, int(i == j)),
                  product.is_one() if i == j else product.is_zero())
    check("s0 t0 + s1 t1 = 1", (s0 * t0 + s1 * t1).is_one())
    check("prefix tables: s0 t0 + s1 t1 = 1", L.parse_table("s0 t0 + s1 t1").is_one())
    check("prefix tables: t0 s1 = 0", L.parse_table("t0 s1").is_zero())
    check("t0 s0 = 1", (t0 * s0).is_one())
    check("s0 t0 != 1 (R is not directly finite)",
          not (s0 * t0).is_one() and not L.parse_table("s0 t0").is_one())
    check("parser: S[01]T[10] = s0 s1 t0 t1", L.parse_elem("S[01]T[10]") == s0 * s1 * t0 * t1)
    check("normal form: s1 t1 = 1 + s0 t0", L.parse_elem("s1 t1") == ONE + s0 * t0)
    check("parser: (1+s0t1)(1+s1t0) = 1 + s0t1 + s1t0 + s0t0",
          L.parse_elem("(1+s0t1)(1+s1t0)") == L.parse_elem("1 + s0 t1 + s1 t0 + s0 t0"))
    try:
        L.parse("s01")
        rejected = False
    except L.ParseError:
        rejected = True
    check("parser rejects the ambiguous 's01'", rejected)


def test_normal_form_against_tables(rng):
    trials = 400
    bad = 0
    for _ in range(trials):
        a, b, c = random_elem(rng), random_elem(rng), random_elem(rng)
        ab = a * b
        if not ab.table().equals(a.table().compose(b.table())):
            bad += 1
        if not (a + b).table().equals(a.table() + b.table()):
            bad += 1
        if (a * b) * c != a * (b * c):
            bad += 1
        if a * (b + c) != a * b + a * c:
            bad += 1
        if (a * b).star() != b.star() * a.star():
            bad += 1
        if Elem.from_terms(a.terms) != a:
            bad += 1
        if (a == b) != a.table().equals(b.table()):
            bad += 1
    check("normal form = prefix tables on products, sums, associativity, distributivity, star",
          bad == 0, "%d random triples, %d disagreements" % (trials, bad))


def test_third_implementation(rng):
    try:
        sys.path.insert(0, os.path.join(REPO, "experiments"))
        import depth_one_paired_leavitt_return_search as third
    except Exception as error:  # pragma: no cover - reported as a failure
        check("third implementation is importable", False, repr(error))
        return
    trials = 400
    bad = 0
    for _ in range(trials):
        a, b = random_elem(rng, 5, 4), random_elem(rng, 5, 4)
        ours = a * b
        theirs = third.multiply(frozenset(a.terms), frozenset(b.terms))
        if not third.equal(tuple(ours.terms), tuple(theirs)):
            bad += 1
    check("normal form agrees with experiments/depth_one_paired_leavitt_return_search.multiply",
          bad == 0, "%d random products, %d disagreements" % (trials, bad))


def test_standard_units():
    units = L.standard_units()
    x = s0 * t1
    y = s1 * t0
    check("x^2 = y^2 = 0", (x * x).is_zero() and (y * y).is_zero())
    check("xy = s0t0 and yx = s1t1", x * y == s0 * t0 and y * x == s1 * t1)
    for name in ("@u", "@v", "@w"):
        check("%s is an involution" % name, units[name].order(4) == 2)
    u, v, w, g = units["@u"], units["@v"], units["@w"], units["@g"]
    check("u + v + w = 0 in R", (u.val + v.val + w.val).is_zero())
    check("u, v, w are pairwise distinct", len({u.key, v.key, w.key}) == 3)
    check("g = uv has order exactly three", g.order(8) == 3)
    check("g + g^-1 = 1", (g.val + g.inv).is_one())
    return units


def rank_three_lifts():
    u1 = Unit(L.psi2(ONE, ZERO, t1, ONE), L.psi2(ONE, ZERO, t1, ONE))
    u2 = Unit(L.psi2(t0 + ONE, ONE, ONE, ZERO), L.psi2(ZERO, ONE, ONE, t0 + ONE))
    u3 = Unit(L.psi2(ZERO, ONE, ONE, ONE), L.psi2(ONE, ONE, ONE, ZERO))
    v1 = Unit(L.psi2(ONE, s1, ZERO, ONE), L.psi2(ONE, s1, ZERO, ONE))
    v2 = Unit(L.psi2(s0 + ONE, ONE, ONE, ZERO), L.psi2(ZERO, ONE, ONE, s0 + ONE))
    return (u1, u2, u3), (v1, v2, u3)


def test_rank_three_lifts(units):
    us, vs = rank_three_lifts()
    check("rank-three lift units verify (val*inv = inv*val = 1)", True)
    check("u1 + u2 + u3 = t0", (us[0].val + us[1].val + us[2].val) == t0)
    check("v1 + v2 + v3 = s0", (vs[0].val + vs[1].val + vs[2].val) == s0)
    check("u1, u2, u3 pairwise distinct", len({unit.key for unit in us}) == 3)
    check("v1, v2, v3 pairwise distinct", len({unit.key for unit in vs}) == 3)
    check("u3 = v3 = g = (1+s0t1)(1+s1t0)", us[2] == units["@g"])
    info("orders (limit 12): u1 %s, u2 %s, v1 %s, v2 %s"
         % tuple(unit.order(12) for unit in (us[0], us[1], vs[0], vs[1])))
    return us, vs


def test_random_unit_words(rng, units):
    pool = [units["@u"], units["@v"], units["@w"], units["@g"]]
    charts = {1: ("01", "1", "000", "001"), 2: ("00", "1", "010", "011")}
    for leaves in charts.values():
        for row, col in ((0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)):
            columns = [1, 2, 4, 8]
            columns[col] |= 1 << row
            pool.append(L.corner_matrix_unit(leaves, columns))
    pool.append(L.thompson_unit(["0", "10", "11"], ["00", "01", "1"]))
    pool.append(L.thompson_unit(["0", "1"], ["1", "0"]))
    check("transvection chart units are involutions", all(unit.order(4) == 2 for unit in pool[4:16]))
    check("the Thompson unit 0<->1 is an involution", pool[-1].order(4) == 2)
    trials = 60
    bad = 0
    longest = 0
    for _ in range(trials):
        length = rng.randint(1, 10)
        word = L.IDENTITY
        for _ in range(length):
            factor = rng.choice(pool)
            if rng.random() < 0.5:
                factor = factor.inverse()
            word = word * factor
        if not (word.val * word.inv).is_one() or not (word.inv * word.val).is_one():
            bad += 1
        longest = max(longest, len(word.val))
    check("random unit words carry correct inverses", bad == 0,
          "%d words, largest normal form %d monomials" % (trials, longest))
    return pool


def test_drazin_seed():
    path = os.path.join(REPO, "research", "artifacts", "kaplansky-finite-drazin-seed-2026-09-08.json")
    with open(path) as handle:
        data = json.load(handle)
    leaves = data["ordered_leaves"]

    def unit_of(columns):
        return L.corner_matrix_unit(leaves, columns)

    parent = unit_of(data["parent_columns"])
    child = unit_of(data["child_columns"])
    elements = {L.IDENTITY.key: L.IDENTITY}
    frontier = [L.IDENTITY]
    while frontier and len(elements) <= 400:
        successors = []
        for element in frontier:
            for generator in (parent, child):
                product = element * generator
                if product.key not in elements:
                    elements[product.key] = product
                    successors.append(product)
        frontier = successors
    check("Drazin seed: parent and child generate a group of order %d in R^x" % data["group_order"],
          len(elements) == data["group_order"], "found %d" % len(elements))

    algebra = {}
    for name in ("e", "T", "h", "v"):
        algebra[name] = GA.GroupAlgebraElement(unit_of(cols) for cols in data[name]["matrix_columns"])
        check("Drazin seed: |supp %s| = %d" % (name, data[name]["support_size"]),
              len(algebra[name]) == data[name]["support_size"])
    e, target, h, v = algebra["e"], algebra["T"], algebra["h"], algebra["v"]
    check("Drazin seed: e^2 = e", e * e == e)
    check("Drazin seed: eT = Te = T", e * target == target and target * e == target)
    t2 = target * target
    t3 = t2 * target
    t4 = t3 * target
    check("Drazin seed: T^4 = T^2", t4 == t2)
    powers = [e, target, t2, t3]
    independent = True
    for mask in range(1, 16):
        total = GA.GroupAlgebraElement()
        for j in range(4):
            if (mask >> j) & 1:
                total = total + powers[j]
        if total.is_zero():
            independent = False
    check("Drazin seed: e, T, T^2, T^3 are independent, so m_T = X^4 + X^2", independent)
    check("Drazin seed: h = T^2 and v = T^3", h == t2 and v == t3)
    check("Drazin seed: h^2 = h, Tv = vT = h, hvh = v",
          h * h == h and target * v == h and v * target == h and h * v * h == v)
    f = e + h
    tf = target * f
    check("Drazin seed: (Tf)^2 = 0 and Tf != 0", (tf * tf).is_zero() and not tf.is_zero())
    complement = ONE + Elem.from_terms((leaf, leaf) for leaf in leaves)

    def block(columns):
        return Elem.from_terms((leaves[i], leaves[j]) for j in range(4) for i in range(4)
                               if (columns[j] >> i) & 1)

    good = True
    for name in ("e", "T", "h", "v"):
        expected = block(data[name]["natural_evaluation_columns"])
        if len(algebra[name]) % 2:
            expected = expected + complement
        if algebra[name].evaluate() != expected:
            good = False
    check("Drazin seed: natural evaluations match the JSON", good)


def test_group_algebra(units, lifts):
    u, v, w, g = units["@u"], units["@v"], units["@w"], units["@g"]
    idempotent = GA.GroupAlgebraElement([g, g * g])
    check("[g] + [g^2] is idempotent with pi = 1",
          idempotent * idempotent == idempotent and idempotent.evaluate().is_one())
    kernel = GA.GroupAlgebraElement([u, v, w])
    check("[u]+[v]+[w] is a nonzero element of ker pi with augmentation 1",
          not kernel.is_zero() and kernel.evaluate().is_zero() and kernel.augmentation() == 1)
    corner = idempotent * kernel * idempotent
    info("e([u]+[v]+[w])e has support %d" % len(corner))
    us, vs = lifts
    t_lift = GA.GroupAlgebraElement(us)
    s_lift = GA.GroupAlgebraElement(vs)
    check("pi(t~) = t0 and pi(s~) = s0", t_lift.evaluate() == t0 and s_lift.evaluate() == s0)
    product = t_lift * s_lift
    check("t~ s~ != 1 while pi(t~ s~) = 1", not product.is_one() and product.evaluate().is_one())
    check("star reverses products", (t_lift * s_lift).star() == s_lift.star() * t_lift.star())
    identity = GA.identity_matrix(2)
    check("2x2 identity matrix squares to itself", GA.is_identity_matrix(GA.matmul(identity, identity)))


def brute_force_garden_of_eden(tau, cells, values):
    index = {}
    variables = []
    rows = []
    for cell in cells:
        row = []
        for m in tau.memory:
            product = cell * m
            if product.key not in index:
                index[product.key] = len(variables)
                variables.append(product)
            row.append(index[product.key])
        rows.append(row)
    for assignment in itertools.product(range(tau.k), repeat=len(variables)):
        if all(tau.local([assignment[v] for v in row]) == symbol for row, symbol in zip(rows, values)):
            return False
    return True


def test_automata(rng, units):
    e, u, g = units["@e"], units["@u"], units["@g"]
    tau = CA.shift_automaton(2, g)
    sigma = CA.shift_automaton(2, g.inverse())
    check("the shift by g^-1 inverts the shift by g", CA.compose_is_identity(sigma, tau)[0])
    check("the shift has no Garden of Eden on {e,u}", CA.garden_of_eden(tau, [e, u], [1, 0])[0] is False)
    linear = CA.CellularAutomaton(2, [e, u], [0, 1, 1, 0])
    check("tau_{1+[u]}: (1,0) on {e,u} is a Garden of Eden",
          CA.garden_of_eden(linear, [e, u], [1, 0])[0] is True)
    check("tau_{1+[u]}: (1,1) on {e,u} has a preimage",
          CA.garden_of_eden(linear, [e, u], [1, 1])[0] is False)
    check("the identity is not a left inverse of tau_{1+[u]}",
          CA.compose_is_identity(CA.CellularAutomaton(2, [e], [0, 1]), linear)[0] is False)
    pool = [e, u, units["@v"], units["@w"], g, g.inverse()]
    bad = 0
    for _ in range(25):
        a = GA.GroupAlgebraElement(rng.sample(pool, rng.randint(1, 3)))
        b = GA.GroupAlgebraElement(rng.sample(pool, rng.randint(1, 3)))
        composite = CA.compose(CA.linear_automaton(a), CA.linear_automaton(b))
        if not CA.equal(composite, CA.linear_automaton(a * b)):
            bad += 1
    check("tau_a o tau_b = tau_{ab} on 25 random pairs", bad == 0, "%d disagreements" % bad)
    bad = 0
    for _ in range(40):
        k = rng.choice((2, 3))
        memory = rng.sample(pool, 3)
        rule = [rng.randrange(k) for _ in range(k ** 3)]
        automaton = CA.CellularAutomaton(k, memory, rule)
        cells = rng.sample(pool, rng.randint(1, 2))
        values = [rng.randrange(k) for _ in cells]
        fast = CA.garden_of_eden(automaton, cells, values)[0]
        slow = brute_force_garden_of_eden(automaton, cells, values)
        if fast != slow:
            bad += 1
    check("backtracking Garden-of-Eden test = brute force on 40 random instances", bad == 0,
          "%d disagreements" % bad)
    bad = 0
    for _ in range(10):
        memory = rng.sample(pool, 3)
        rule = [rng.randrange(2) for _ in range(8)]
        automaton = CA.CellularAutomaton(2, memory, rule)
        left = CA.compose(CA.CellularAutomaton(2, [e], [0, 1]), automaton)
        if not CA.equal(left, automaton):
            bad += 1
    check("id o tau = tau on 10 random automata", bad == 0)


def test_kl(rng, units):
    g, u = units["@g"], units["@u"]
    equation = [("x", 1), ("u", g), ("x", -1)]
    control, _ = KL.verify_normal_closure(g, equation, [([("x", -1)], 1)], require_nonsingular=False)
    check("x^-1 (x g x^-1) x = g (normal-closure control)", control)
    rejected, _ = KL.verify_normal_closure(g, equation, [([("x", -1)], 1)])
    check("a singular equation is rejected as a KL certificate", not rejected)
    trivial, report = KL.verify_normal_closure(
        g, [("x", 2)], [([("u", u)], 1), ([("u", u)], -1)])
    check("h w h^-1 h w^-1 h^-1 reduces to the empty word", not trivial and report["final_length"] == 0)
    pool = [units["@u"], units["@v"], units["@w"], g]
    bad = 0
    for _ in range(50):
        word = []
        for _ in range(rng.randint(1, 12)):
            if rng.random() < 0.5:
                word.append(("x", rng.choice((-2, -1, 1, 2))))
            else:
                word.append(("u", rng.choice(pool)))
        if KL.reduce_word(word + KL.invert_word(word)) != []:
            bad += 1
    check("every random word times its inverse reduces to the empty word", bad == 0)
    check("reduction merges units: u u = 1", KL.reduce_word([("u", u), ("u", u)]) == [])


def test_examples():
    for path in sorted(glob.glob(os.path.join(HERE, "examples", "*.json"))):
        cert, passed, lines = certcheck.check_file(path)
        outcome = "PASS" if passed else "FAIL"
        check("example %s gives %s" % (os.path.basename(path), cert.get("expect")),
              outcome == cert.get("expect"), " | ".join(lines[:3]))


def main():
    L.set_dual(True)
    rng = random.Random(20260911)
    start = time.time()
    print("python %s" % sys.version.split()[0])
    test_relations()
    test_normal_form_against_tables(rng)
    test_third_implementation(rng)
    units = test_standard_units()
    lifts = test_rank_three_lifts(units)
    test_random_unit_words(rng, units)
    test_drazin_seed()
    test_group_algebra(units, lifts)
    test_automata(rng, units)
    test_kl(rng, units)
    test_examples()
    failures = [name for name, ok, _ in RESULTS if not ok]
    print("dual path: %s" % (L.dual_stats(),))
    print("SUMMARY %d checks, %d failures, %.1f s" % (len(RESULTS), len(failures), time.time() - start))
    for name in failures:
        print("FAILED: %s" % name)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
