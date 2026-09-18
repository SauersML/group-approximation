"""Search for rotation twists of a finite set S of elements of F that generate a VIRTUALLY ABELIAN
(hence amenable) subgroup of Thompson's T, with an exact certificate.

For twists h_i = f_i rho_{theta_i}: find a finite orbit O of H = <h_i> (candidate points: breakpoints
of the h_i and their inverses, endpoints of the maximal invariant subset of the intersection of the
Per(h_i)), compute the permutation action of H on O, a Schreier transversal of the kernel H_0 (the
pointwise stabilizer of O, finite index), and the Schreier generators of H_0.  If the Schreier
generators pairwise commute, H_0 is abelian and H is virtually abelian: an exact amenability
certificate.  Then the points R_D, f_1 R_D, ..., f_n R_D of T/R_D lie in one orbit of an amenable
subgroup, so S is NOT a witness for thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive.
"""
from fractions import Fraction as Q
import itertools, json, os, sys

sys.path.insert(0, os.path.dirname(__file__))
from finite_orbit_census import (PL, compose, rot, X0, X1, ID, fix_set, intersect, period,
                                 max_invariant, orbit)  # noqa: E402

IDK = ID.key()


def mod1(x):
    return x - (x // 1)


def finite_orbits(gens, PB=200, OB=200):
    invs = [g.inverse() for g in gens]
    W = [(Q(0), Q(1))]
    for g in gens:
        q, P = period(g, PB)
        if q is None:
            return []
        W = intersect(W, P)
        if not W:
            return []
    M, _ = max_invariant(W, gens + invs)
    if not M:
        return []
    cands = {l for l, r in M} | {mod1(r) for l, r in M}
    for g in gens + invs:
        cands |= set(g.xs)
    orbs = []
    for c in sorted(cands):
        if not any(l <= c <= r for l, r in M):
            continue
        o = orbit(c, gens + invs, OB)
        if o is not None and o not in orbs:
            orbs.append(o)
    return orbs


def perm_of(g, O):
    idx = {x: i for i, x in enumerate(O)}
    return tuple(idx[mod1(g(x))] for x in O)


def schreier(gens, O, TB=5000):
    """Transversal of H/H_0 (H_0 = kernel of the action on O) and Schreier generators of H_0."""
    allg = gens + [g.inverse() for g in gens]
    perms = [perm_of(g, O) for g in allg]
    e = tuple(range(len(O)))
    trans = {e: ID}
    fr = [e]
    while fr:
        nf = []
        for p in fr:
            for g, s in zip(allg, perms):
                q = tuple(s[p[i]] for i in range(len(O)))  # perm of g o t_p
                if q not in trans:
                    trans[q] = compose(g, trans[p])
                    nf.append(q)
                    if len(trans) > TB:
                        return None, None
        fr = nf
    sg = {}
    for p, t in trans.items():
        for g, s in zip(allg, perms):
            q = tuple(s[p[i]] for i in range(len(O)))
            u = compose(trans[q].inverse(), compose(g, t))
            if u.key() != IDK:
                sg[u.key()] = u
    return trans, list(sg.values())


def all_commute(els):
    for i in range(len(els)):
        for j in range(i + 1, len(els)):
            if compose(els[i], els[j]).key() != compose(els[j], els[i]).key():
                return False
    return True


def certify_virtually_abelian(gens):
    for O in finite_orbits(gens):
        trans, sg = schreier(gens, O)
        if trans is None:
            continue
        if all_commute(sg):
            return {"orbit": [str(x) for x in O], "index": len(trans),
                    "abelian_kernel_generators": len(sg)}
    return None


def fmap(f):
    return {"xs": [str(x) for x in f.xs], "ys": [str(y) for y in f.ys]}


X2 = compose(X0.inverse(), compose(X1, X0))

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "x0x1"
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    S = {"x0x1": [X0, X1], "x0x1x2": [X0, X1, X2],
         "x0x1_x0x1": [X0, X1, compose(X0, X1)]}[which]
    N = 2 ** K
    tw = [Q(i, N) for i in range(N)]
    found = []
    for th in itertools.product(tw, repeat=len(S)):
        gens = [compose(f, rot(t)) for f, t in zip(S, th)]
        c = certify_virtually_abelian(gens)
        if c:
            c["twists"] = [str(t) for t in th]
            found.append(c)
    print(json.dumps({"S": which, "K": K, "tuples": N ** len(S),
                      "virtually_abelian_twists": found}, indent=1))
