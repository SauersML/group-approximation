#!/usr/bin/env python3
"""Replay Step 4 of the Thompson-Steinberg completeness proof as a checked case table.

Each of the 43 relators of the families (B), (C), (P), (Q) of the sixty-relator presentation maps,
under beta, to leaf transvections T(alpha, beta) in the chart D = (00, 01, 10, 110, 111).  This
script classifies every image by the rules consumed in the proof, checking their cone side
conditions:
  B-dis [T(al,be), T(ga,de)] = 1         four pairwise disjoint cones, nonempty complement
  B-src [T(al,be), T(al,ga)] = 1         al, be, ga pairwise disjoint, nonempty complement
  B-tgt [T(al,ga), T(be,ga)] = 1         same
  C11   [T(al,be), T(be,ga)] = T(al,ga)  al, be, ga pairwise disjoint, nonempty complement
  C1d   [T(al,be), T(be d,ga)] = T(al d,ga)
  CEd   [T(al,be d), T(be,ga)] = T(al,ga d)
  Z     [T(al,be), T(de,ga)] = 1 via B-dis (al, be, de, ga pairwise disjoint)
It also checks every rule output against the Steinberg product computed in the ring,
x_ik(lm) = 1 + S[d_i] l m T[d_k].  Pure combinatorics; no Leavitt arithmetic.
"""
import itertools
import json
import sys

D = ["00", "01", "10", "110", "111"]
LET = {"1": ("", ""), "e": ("0", ""), "f": ("1", ""), "E": ("", "0"), "F": ("", "1")}
A = list(LET)


def mono_mul(x, y):
    """(S[p1]T[q1]) (S[p2]T[q2]) as (p, q) or None."""
    (p1, q1), (p2, q2) = x, y
    if p2.startswith(q1):
        return (p1 + p2[len(q1):], q2)
    if q1.startswith(p2):
        return (p1, q2 + q1[len(p2):])
    return None


def X(i, j, l):
    s, t = LET[l]
    return (D[i] + s, D[j] + t)


def X_prod(i, k, l, m):
    mono = mono_mul(LET[l], LET[m])
    return None if mono is None else (D[i] + mono[0], D[k] + mono[1])


def disjoint(cones):
    return all(not (a.startswith(b) or b.startswith(a)) for a, b in itertools.combinations(cones, 2))


def proper(cones):
    return disjoint(cones) and sum(2.0 ** -len(c) for c in cones) < 1.0


def rule_B(c1, c2):
    (al, be), (ga, de) = c1, c2
    if proper([al, be, ga, de]):
        return "B-dis"
    if al == ga and be != de and proper([al, be, de]):
        return "B-src"
    if be == de and al != ga and proper([al, ga, be]):
        return "B-tgt"
    return None


def rule_C(c1, c2):
    """Return (rule, output) for [T(c1), T(c2)], or (None, None)."""
    (al, be), (bp, ga) = c1, c2
    if bp == be and proper([al, be, ga]):
        return "C11", (al, ga)
    for d in "01":
        if bp == be + d and proper([al, be, ga]):
            return "C1d(d=" + d + ")", (al + d, ga)
        if be == bp + d and proper([al, bp, ga]):
            return "CEd(d=" + d + ")", (al, ga + d)
    if proper([al, be, bp, ga]):
        return "Z (B-dis)", None
    return None, None


def main():
    table, bad = [], []
    for a, b in itertools.combinations_with_replacement(A, 2):
        r = rule_B(X(0, 1, a), X(2, 3, b))
        table.append(("B", "[X12(%s),X34(%s)]" % (a, b), r))
        bad += [] if r == "B-dis" else [table[-1]]
    for name, c2, want in (("[X12(1),X13(1)]", X(0, 2, "1"), "B-src"), ("[X12(1),X32(1)]", X(2, 1, "1"), "B-tgt")):
        r = rule_B(X(0, 1, "1"), c2)
        table.append(("B", name, r))
        bad += [] if r == want else [table[-1]]
    for a, b in itertools.product(A, repeat=2):
        rule, outp = rule_C(X(0, 1, a), X(1, 2, b))
        ring = X_prod(0, 2, a, b)
        mono = mono_mul(LET[a], LET[b])
        reducing = mono is None or (mono[0] + mono[1] in ("", "0", "1") and (mono[0] == "" or mono[1] == ""))
        if reducing:
            table.append(("C", "[X12(%s),X23(%s)] = X13(%s)" % (a, b, "0" if mono is None else a + b), rule))
            if rule is None or outp != ring:
                bad.append(table[-1] + (outp, ring))
        else:
            rule2, outp2 = rule_C(X(0, 3, a), X(3, 2, b))
            table.append(("P", "[X12(%s),X23(%s)] = [X14(%s),X43(%s)]" % (a, b, a, b), "%s | %s" % (rule, rule2)))
            if rule is None or rule2 is None or outp != ring or outp2 != ring:
                bad.append(table[-1] + (outp, outp2, ring))
    r1, o1 = rule_C(X(0, 1, "e"), X(1, 2, "E"))
    r2, o2 = rule_C(X(0, 1, "f"), X(1, 2, "F"))
    al, ga = X(0, 2, "1")
    split_ok = o1 == (al + "0", ga + "0") and o2 == (al + "1", ga + "1") and proper([al, ga])
    table.append(("Q", "[X12(e),X23(E)][X12(f),X23(F)] = X13(1)", "%s, %s, split %s" % (r1, r2, split_ok)))
    if not split_ok:
        bad.append(table[-1])
    counts = {}
    for fam, _n, _r in table:
        counts[fam] = counts.get(fam, 0) + 1
    out = {"relators_replayed": len(table), "by_family": counts, "failures": [list(map(str, b)) for b in bad],
           "verdict": "PASS" if not bad else "FAIL",
           "table": [{"family": f, "relator": n, "rule": r} for f, n, r in table]}
    print(json.dumps({k: v for k, v in out.items() if k != "table"}, indent=1))
    for f, n, r in table:
        print("%s | %-44s | %s" % (f, n, r))
    with open("replay-thompson-steinberg-derivation.json", "w") as fh:
        json.dump(out, fh, indent=1)
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main())
