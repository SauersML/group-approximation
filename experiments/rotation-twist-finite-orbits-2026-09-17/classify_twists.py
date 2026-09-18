"""Classify every dyadic rotation twist (denominator 2^K) of a finite S in F, exactly.

For H = <f_i rho_{theta_i}> one of:
  no-finite-orbit   the maximal H-invariant subset of the intersection of Per(w), w over words of
                    length <= LW, is empty; then H has no finite orbit, so H is NONAMENABLE
                    (finitely generated amenable subgroups of T have finite orbits), unconditionally.
  contains-F        a pair of words of length <= LP with a common fixed point has an orbital with a
                    one-sided approach (Brin Theorem 1): H contains a copy of F.
  virtually-abelian Schreier generators of the pointwise stabilizer of a finite orbit commute: H amenable.
  unresolved        none of the above.
"""
from fractions import Fraction as Q
import itertools, json, os, sys

sys.path.insert(0, os.path.dirname(__file__))
from finite_orbit_census import compose, rot, X0, X1, ID, fix_set, intersect, period, max_invariant, words  # noqa
from brin_certify import orbitals, moves_right_of, moves_left_of, fold  # noqa: E402
from amenable_twist_search import certify_virtually_abelian, X2  # noqa: E402

IDK = ID.key()


def has_no_finite_orbit(gens, LW, PB=200):
    """True only if (i) every generator has a periodic point (so rot(H) is finite whenever H preserves a
    probability measure) and (ii) no finite H-orbit exists.  Then H is nonamenable."""
    for g in gens:
        if period(g, PB)[0] is None:
            return False
    W = [(Q(0), Q(1))]
    for _, g in words(gens, LW):
        q, P = period(g, PB)
        if q is None:
            continue
        W = intersect(W, P)
        if not W:
            return True
    M, _ = max_invariant(W, gens + [g.inverse() for g in gens])
    return not M


def contains_F(gens, LP):
    els, seen = [], set()
    for w, g in words(gens, LP):
        k = g.key()
        if k == IDK or k in seen:
            continue
        seen.add(k)
        fx = fix_set(g)
        if fx:
            els.append((w, fx))
    for i in range(len(els)):
        for j in range(i, len(els)):
            Phi = intersect(els[i][1], els[j][1])
            if not Phi:
                continue
            for (u, v) in orbitals(Phi):
                for w, fx in (els[i], els[j]):
                    if moves_right_of(fx, u) != moves_left_of(fx, fold(v)):
                        return {"pair": [list(map(list, els[i][0])), list(map(list, els[j][0]))],
                                "orbital": [str(u), str(v)]}
    return None


SETS = {"x0x1": [X0, X1], "x0x1x2": [X0, X1, X2]}

if __name__ == "__main__":
    which = sys.argv[1]
    K = int(sys.argv[2])
    LW = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    LP = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    S = SETS[which]
    N = 2 ** K
    tw = [Q(i, N) for i in range(N)]
    counts = {"no-finite-orbit": 0, "contains-F": 0, "virtually-abelian": 0, "unresolved": 0}
    detail = []
    for th in itertools.product(tw, repeat=len(S)):
        gens = [compose(f, rot(t)) for f, t in zip(S, th)]
        if has_no_finite_orbit(gens, LW):
            counts["no-finite-orbit"] += 1
            continue
        va = certify_virtually_abelian(gens)
        if va:
            counts["virtually-abelian"] += 1
            detail.append({"twists": list(map(str, th)), "class": "virtually-abelian", "cert": va})
            continue
        cf = contains_F(gens, LP)
        if cf:
            counts["contains-F"] += 1
            detail.append({"twists": list(map(str, th)), "class": "contains-F", "cert": cf})
            continue
        counts["unresolved"] += 1
        detail.append({"twists": list(map(str, th)), "class": "unresolved"})
    print(json.dumps({"S": which, "K": K, "word_length_orbits": LW, "word_length_pairs": LP,
                      "counts": counts, "detail": detail}, indent=1))
