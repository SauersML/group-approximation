#!/usr/bin/env python3
"""Exponent / eigenvalue classification of the (3,1,3) length-15 words behind the obstruction
in research/mapping-torus-targets-fail-rank-2-window-one-relators.md.

For each word s of the list, and each span-2 Magnus rewrite r' of s with occurrence pattern
(3,1,3) (the middle letter a_1 once), let e = (e0, e1, e2) be the exponent vector and
f(x) = e2 x^2 + e1 x + e0.  The script checks, and aborts on failure:
  * e1 = +-1 and e0 + e1 + e2 is odd (so nonzero): a is torsion in H_1(G), and every
    residually torsion-free nilpotent target kills a (item 1 of the node);
  * f is primitive and its discriminant 1 - 4 e0 e2 is not a square, so f is irreducible
    over Q; hence a root of f is an algebraic integer iff |e2| = 1, and the inverse of a root
    is one iff |e0| = 1 (items 2 and 3).
Then every word is put in one class
  KILL      |e0| = |e2| = 3: no target of either kind in items 2, 3;
  ASC       exactly one of |e0|, |e2| is 1: killed for (f.g. res. t.f. nilpotent)-by-Z targets,
            open only for ascending mapping tori with T of the admissible sign;
  UNIT      |e0| = |e2| = 1: the roots are units (6th roots of unity or golden-ratio units);
and the class counts are printed.  A word with several (3,1,3) rewrites keeps the weakest
class (the obstruction must hold for G, whichever rewrite is used).

Usage: eigen_obstruction.py WORDFILE [-v]     (eigen-L15.txt: eigen_obstruction.py w313-L15.txt -v)
"""
import math, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.chdir(HERE)
from classify import rewrites  # noqa: E402

RANK = {"KILL": 0, "ASC": 1, "UNIT": 2}


def klass(e0, e1, e2):
    assert abs(e1) == 1, (e0, e1, e2)
    assert (e0 + e1 + e2) % 2 == 1, (e0, e1, e2)
    assert math.gcd(math.gcd(abs(e0), abs(e1)), abs(e2)) == 1
    d = 1 - 4 * e0 * e2
    assert d < 0 or math.isqrt(d) ** 2 != d, (e0, e1, e2)
    u0, u2 = abs(e0) == 1, abs(e2) == 1
    return "UNIT" if u0 and u2 else ("ASC" if u0 or u2 else "KILL")


def main():
    words = open(sys.argv[1]).read().split()
    count, poly = {}, {}
    for s in words:
        best = None
        for r, ev, occ in rewrites(s):
            if occ != [3, 1, 3]:
                continue
            k = klass(*ev)
            if best is None or RANK[k] > RANK[best[0]]:
                best = (k, tuple(ev))
        assert best is not None, s
        count[best[0]] = count.get(best[0], 0) + 1
        if best[0] == "UNIT":
            e0, e1, e2 = best[1]
            key = "x^2 %s x %s 1" % ("+" if e1 * e2 > 0 else "-", "+" if e0 * e2 > 0 else "-")
            poly[key] = poly.get(key, 0) + 1
        if "-v" in sys.argv:
            print(s, best[0], best[1])
    print("# %d words:" % len(words), ", ".join("%s %d" % (k, count.get(k, 0)) for k in RANK))
    print("# UNIT words by f/e2:", ", ".join("%s: %d" % kv for kv in sorted(poly.items())))
    print("EXIT 0")


if __name__ == "__main__":
    main()
