"""Certify a copy of F inside the finite-orbit twists found by finite_orbit_census.py.

For a twist H = <A, B>, A = x0 rho_a, B = x1 rho_b, with a certified finite orbit O, collect the words
of length <= L that fix O pointwise; they generate a subgroup G of the pointwise stabilizer H_0.
Cutting S^1 at a point of O makes G a subgroup of PL_o(I).  The orbitals of G are the components of
S^1 minus the common fixed set of the chosen generators.  Brin's Theorem 1
(research/brin-plo-i-one-sided-approach-gives-a-copy-of-f.md): if some element of G approaches one end
of an orbital but not the other, G contains F.  We test that criterion on the chosen generators;
a hit is an exact certificate that H contains a copy of F.
"""
from fractions import Fraction as Q
import json, os, sys

sys.path.insert(0, os.path.dirname(__file__))
from finite_orbit_census import (compose, rot, X0, X1, fix_set, intersect, words, fmt)  # noqa: E402


def moves_right_of(fixarcs, u):
    """True iff the map is not the identity on (u, u + eps)."""
    for l, r in fixarcs:
        if l <= u < r:
            return False
    if u == 0:
        return True
    return True


def moves_left_of(fixarcs, v):
    """True iff the map is not the identity on (v - eps, v); v in (0, 1]."""
    for l, r in fixarcs:
        if l < v <= r:
            return False
    return True


def orbitals(Phi):
    """Gaps of the closed set Phi (sorted merged arcs in [0,1], nonempty) as (u, v) with v possibly > 1."""
    gaps = []
    n = len(Phi)
    for i in range(n):
        u = Phi[i][1]
        if i + 1 < n:
            v = Phi[i + 1][0]
        else:
            v = Phi[0][0] + 1
        if u < v and not (u == 1 and v == 1):
            if u == 1:
                u, v = Q(0), v - 1
            gaps.append((u, v))
    return [g for g in gaps if g[0] < g[1]]


def fold(v):
    return v - 1 if v > 1 else v


def certify(a, b, O, L):
    A = compose(X0, rot(a))
    B = compose(X1, rot(b))
    gens = []
    for w, g in words([A, B], L):
        ok = True
        for x in O:
            y = g(x)
            if y - (y // 1) != x:
                ok = False
                break
        if ok and g.key() != compose(X0, X0.inverse()).key():
            gens.append((w, g, fix_set(g)))
    if not gens:
        return {"status": "no-stabilizer-words"}
    Phi = [(Q(0), Q(1))]
    for _, _, fx in gens:
        Phi = intersect(Phi, fx)
    orbs = orbitals(Phi)
    for (u, v) in orbs:
        for w, g, fx in gens:
            left = moves_right_of(fx, u)
            right = moves_left_of(fx, fold(v)) if v != 1 else moves_left_of(fx, Q(1))
            # an element counts only if its support meets the orbital near an end
            if left != right:
                return {"status": "contains-F", "orbital": [str(u), str(v)],
                        "witness_word": [[i, e] for i, e in w],
                        "approaches": "left end only" if left else "right end only",
                        "stabilizer_words": len(gens)}
    return {"status": "criterion-not-met", "orbitals": [[str(u), str(v)] for u, v in orbs],
            "stabilizer_words": len(gens)}


def pair_certify(a, b, L):
    """Search pairs (g, h) of words of length <= L in H with a common fixed point such that one of g, h
    approaches exactly one end of an orbital of <g, h>.  A hit certifies F <= <g, h> <= H by Brin's
    Theorem 1 (cut S^1 at a common fixed point of g and h to land in PL_o(I))."""
    A = compose(X0, rot(a))
    B = compose(X1, rot(b))
    idk = compose(X0, X0.inverse()).key()
    els = []
    seen = set()
    for w, g in words([A, B], L):
        k = g.key()
        if k == idk or k in seen:
            continue
        seen.add(k)
        fx = fix_set(g)
        if fx:
            els.append((w, g, fx))
    for i in range(len(els)):
        for j in range(i, len(els)):
            wi, gi, fi = els[i]
            wj, gj, fj = els[j]
            Phi = intersect(fi, fj)
            if not Phi:
                continue
            for (u, v) in orbitals(Phi):
                for w, fx in ((wi, fi), (wj, fj)):
                    left = moves_right_of(fx, u)
                    right = moves_left_of(fx, fold(v))
                    if left != right:
                        return {"status": "contains-F",
                                "pair": [[list(x) for x in wi], [list(x) for x in wj]],
                                "orbital": [str(u), str(v)],
                                "one_sided_element": [list(x) for x in w]}
    return {"status": "no-certificate", "elements_with_fixed_points": len(els)}


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "pairs":
    census = json.load(open(sys.argv[2]))
    L = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    res = []
    for r in census["pairs_not_excluded"]:
        c = pair_certify(Q(r["a"]), Q(r["b"]), L)
        c.update({"a": r["a"], "b": r["b"], "finite_orbits": r["certified_finite_orbits"]})
        res.append(c)
    print(json.dumps({"K": census["K"], "word_length": L, "results": res}, indent=1))
    sys.exit(0)

if __name__ == "__main__":
    census = json.load(open(sys.argv[1]))
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    res = []
    for r in census["pairs_not_excluded"]:
        a, b = Q(r["a"]), Q(r["b"])
        for o in r["certified_finite_orbits"]:
            O = [Q(x) for x in o]
            c = certify(a, b, O, L)
            c.update({"a": r["a"], "b": r["b"], "orbit": o})
            res.append(c)
    print(json.dumps({"K": census["K"], "word_length": L, "results": res}, indent=1))
