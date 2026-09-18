#!/usr/bin/env python3
"""Certify <a,b | w> by trying every automorphic image of w (Nielsen moves on F(a,b))
up to length len(w)+slack.  Usage: orbit_certify.py 'A A B A B A A b b' [slack]"""
import sys
from hierarchy_certify import certify, cred, canon, subst, parse, is_proper_power


def moves():
    L = []
    for x, y in (("a", "b"), ("b", "a")):
        for ey in (1, -1):
            L.append({x: ((x, 1), (y, ey))})
            L.append({x: ((y, ey), (x, 1))})
    return L


def orbit(w, slack):
    w = cred(w)
    bound = len(w) + slack
    seen = {canon(w): w}
    frontier = [w]
    mv = moves()
    while frontier:
        nf = []
        for u in frontier:
            for m in mv:
                v = cred(subst(u, m))
                if len(v) > bound:
                    continue
                k = canon(v)
                if k not in seen:
                    seen[k] = v
                    nf.append(v)
        frontier = nf
    return list(seen.values())


def orbit_certify(w, slack=4, memo=None):
    memo = {} if memo is None else memo
    for v in sorted(orbit(w, slack), key=len):
        ok, why = certify(v, "new", memo=memo)
        if ok:
            return True, v, why
    return False, None, None


if __name__ == "__main__":
    w = parse(sys.argv[1])
    print(orbit_certify(w, int(sys.argv[2]) if len(sys.argv) > 2 else 4))
