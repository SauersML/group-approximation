"""Deeper Brin search for a twist left unresolved by classify_twists.py.

Take a finite orbit O of H, the Schreier generators s_1..s_k of the pointwise stabilizer H_0 of O,
and all products of at most D of them (and inverses).  For every pair (g, h) of these elements with a
common fixed point, test Brin's Theorem 1 on each orbital of <g, h>: some element of the pair is the
identity near one end of the orbital and not near the other.  Usage: brin_deep.py a b D
(twist of {x0, x1} by (a, b)), or brin_deep.py explicit a b WORD1 WORD2 to check one pair of words
over the letters A, a = A^-1, B, b = B^-1 (A = x0 rho_a, B = x1 rho_b; a word is a composite, leftmost
letter applied last).
"""
from fractions import Fraction as Q
import itertools, json, os, sys

sys.path.insert(0, os.path.dirname(__file__))
from finite_orbit_census import compose, rot, X0, X1, ID, fix_set, intersect  # noqa: E402
from brin_certify import orbitals, moves_right_of, moves_left_of, fold  # noqa: E402
from amenable_twist_search import finite_orbits, schreier  # noqa: E402

IDK = ID.key()


def products(gens, D):
    allg = gens + [g.inverse() for g in gens]
    out = {IDK: ((), ID)}
    fr = [((), ID)]
    for _ in range(D):
        nf = []
        for w, g in fr:
            for i, s in enumerate(allg):
                h = compose(s, g)
                k = h.key()
                if k not in out:
                    out[k] = (w + (i,), h)
                    nf.append((w + (i,), h))
        fr = nf
    return [v for k, v in out.items() if k != IDK]


def brin_pair(els):
    fx = [(w, g, fix_set(g)) for w, g in els]
    fx = [t for t in fx if t[2]]
    for i in range(len(fx)):
        for j in range(i, len(fx)):
            Phi = intersect(fx[i][2], fx[j][2])
            if not Phi:
                continue
            for (u, v) in orbitals(Phi):
                for w, g, f in (fx[i], fx[j]):
                    if moves_right_of(f, u) != moves_left_of(f, fold(v)):
                        return {"pair_in_schreier_letters": [list(fx[i][0]), list(fx[j][0])],
                                "orbital": [str(u), str(v)], "approaching_element": list(w)}
    return None


def word_map(word, gens):
    """word over letters A, a (= A^-1), B, b (= B^-1), read as a composite l_1 o l_2 o ... ."""
    lt = {"A": gens[0], "a": gens[0].inverse(), "B": gens[1], "b": gens[1].inverse()}
    g = ID
    for ch in reversed(word):
        g = compose(lt[ch], g)
    return g


def explicit(a, b, w1, w2):
    """Check Brin's criterion for the explicit pair of words (w1, w2) in the twist (a, b)."""
    gens = [compose(X0, rot(a)), compose(X1, rot(b))]
    g, h = word_map(w1, gens), word_map(w2, gens)
    fg, fh = fix_set(g), fix_set(h)
    Phi = intersect(fg, fh)
    out = {"twist": [str(a), str(b)], "words": [w1, w2],
           "fix": [[[str(l), str(r)] for l, r in fg], [[str(l), str(r)] for l, r in fh]],
           "common_fix": [[str(l), str(r)] for l, r in Phi], "certified": None}
    for (u, v) in orbitals(Phi):
        for w, f in ((w1, fg), (w2, fh)):
            if moves_right_of(f, u) != moves_left_of(f, fold(v)):
                out["certified"] = {"orbital": [str(u), str(v)], "approaching_exactly_one_end": w}
                return out
    return out


if __name__ == "__main__":
    if sys.argv[1] == "explicit":
        print(json.dumps(explicit(Q(sys.argv[2]), Q(sys.argv[3]), sys.argv[4], sys.argv[5]), indent=1))
        sys.exit(0)
    a, b, D = Q(sys.argv[1]), Q(sys.argv[2]), int(sys.argv[3])
    gens = [compose(X0, rot(a)), compose(X1, rot(b))]
    res = {"twist": [str(a), str(b)], "depth": D, "orbits": []}
    for O in finite_orbits(gens):
        trans, sg = schreier(gens, O)
        entry = {"orbit": [str(x) for x in O], "schreier_generators": len(sg)}
        if trans is not None:
            entry["brin"] = brin_pair(products(sg, D))
        res["orbits"].append(entry)
    print(json.dumps(res, indent=1))
