#!/usr/bin/env python3
"""Independent certificate check for the presentation found by sc_search.py.

Checks, with a different algorithm (all subwords of all cyclic words, counted
by occurrence position), that <x, y | R1, R2, R3> satisfies C'(1/6):
every piece u (a word occurring at two different positions of the symmetrized
closure, i.e. as a common prefix of two distinct cyclic conjugates of the
relators or their inverses) has |u| < |r|/6 for each relator r it lies in.
Also checks cyclic reduction, primitivity, token shapes, and computes H_1.
Letters: x=1, X=-1, y=2, Y=-2.
"""
import json, sys
from fractions import Fraction

def reduce(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return out

def inverse(w):
    return [-a for a in reversed(w)]

def build(tokens):
    w = []
    for t, e in tokens:
        w += t * e
    return w

def r1(ex):  # positive in x, y
    return build([(t, e) for pair in ex for t, e in (([1], pair[0]), ([2], pair[1]))])

def r2(ex):  # positive in tokens x, Yx
    return build([(t, e) for pair in ex for t, e in (([1], pair[0]), ([-2, 1], pair[1]))])

def r3(ex):  # positive in tokens y, Xy
    return build([(t, e) for pair in ex for t, e in (([2], pair[0]), ([-1, 2], pair[1]))])

def check(data):
    rels = [r1(data["R1_syllables_x_y"]), r2(data["R2_syllables_x_Yx"]), r3(data["R3_syllables_y_Xy"])]
    report = {"lengths": [len(r) for r in rels]}
    # shapes and reduction
    for i, r in enumerate(rels):
        assert reduce(r) == r, f"R{i+1} not freely reduced"
        assert r[0] != -r[-1], f"R{i+1} not cyclically reduced"
        n = len(r)
        assert all(not (n % d == 0 and r == r[d:] + r[:d]) for d in range(1, n)), f"R{i+1} is a proper power"
    assert set(rels[0]) == {1, 2}
    assert set(rels[1]) == {1, -2} and all(rels[1][(k + 1) % len(rels[1])] == 1 for k, a in enumerate(rels[1]) if a == -2)
    assert set(rels[2]) == {2, -1} and all(rels[2][(k + 1) % len(rels[2])] == 2 for k, a in enumerate(rels[2]) if a == -1)
    # symmetrized closure: (relator index, orientation, rotation) -> cyclic word
    words = []
    for i, r in enumerate(rels):
        for o, s in enumerate((r, inverse(r))):
            for k in range(len(s)):
                words.append(((i, o, k), s[k:] + s[:k]))
    # a piece: common prefix of two distinct elements of the closure
    worst = Fraction(0)
    worst_info = None
    for a in range(len(words)):
        ka, u = words[a]
        for b in range(len(words)):
            if a == b:
                continue
            kb, v = words[b]
            if u == v:
                raise AssertionError(f"closure has equal distinct elements {ka} {kb}")
            m = 0
            L = min(len(u), len(v))
            while m < L and u[m] == v[m]:
                m += 1
            fr = Fraction(m, len(u))
            if fr > worst:
                worst, worst_info = fr, (ka, kb, m)
    report["max_piece_over_length"] = str(worst)
    report["max_piece_float"] = float(worst)
    report["worst"] = worst_info
    report["C_prime_one_sixth"] = worst < Fraction(1, 6)
    # H_1: exponent sums
    ex = [[r.count(1) - r.count(-1), r.count(2) - r.count(-2)] for r in rels]
    report["exponent_sums"] = ex
    # Smith normal form invariants of 3x2 integer matrix via gcds
    from math import gcd
    d1 = 0
    for row in ex:
        for v in row:
            d1 = gcd(d1, abs(v))
    minors = [ex[i][0] * ex[j][1] - ex[i][1] * ex[j][0] for i in range(3) for j in range(i + 1, 3)]
    d2 = 0
    for m in minors:
        d2 = gcd(d2, abs(m))
    report["H1_invariants"] = [d1, (d2 // d1) if d1 else 0]
    report["relators"] = ["".join({1: "x", -1: "X", 2: "y", -2: "Y"}[a] for a in r) for r in rels]
    return report

if __name__ == "__main__":
    data = json.loads(open(sys.argv[1]).read())
    print(json.dumps(check(data), indent=1))
