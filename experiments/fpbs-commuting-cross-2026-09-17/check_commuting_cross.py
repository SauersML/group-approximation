"""Brute-force check of the commuting-cross witness against the necessary
condition (a) of fpbs-cs-set-family-hypothesis-fails-infinite-centre.

A point a of a finite set A is GOOD if some h in B(R) has a h a^-1 not in A A^-1,
equivalently (a h a^-1) A is disjoint from A.  SF(H,R) for any family forces
#good >= #A/2.  The commuting-cross witness is

    A = X*Y  u  C1  u  C2,   C1 = {x h^-1 x^-1},  C2 = {y h y^-1 h^-1},

x in X (inside H), y in Y (inside the normal factor K), h in B(R).  The claim
is that every point of X*Y is bad, so #good <= #(A minus X*Y) < #A/2 once
#X = #Y = n > 2 #B(R).

Groups: G = H x K with each factor a free product of copies of Z (lower-case
letter, inverse = upper case) and Z/2 (letters listed in INVOL).  Elements are
pairs of reduced words.  Membership in A A^-1 is tested by brute force over A,
not by the algebraic identity.
"""
import itertools, sys

INVOL = set("st")          # involution letters (Z/2 free factors)

def inv_letter(c):
    if c in INVOL:
        return c
    return c.swapcase()

def reduce_word(w):
    out = []
    for c in w:
        if out and out[-1] == inv_letter(c):
            out.pop()
        else:
            out.append(c)
    return "".join(out)

def winv(w):
    return "".join(inv_letter(c) for c in reversed(w))

def mul(g, h):
    return (reduce_word(g[0] + h[0]), reduce_word(g[1] + h[1]))

def inv(g):
    return (winv(g[0]), winv(g[1]))

E = ("", "")

def ball(S, R):
    B = {E}
    frontier = {E}
    for _ in range(R):
        new = set()
        for g in frontier:
            for s in S:
                x = mul(g, s)
                if x not in B:
                    new.add(x)
        B |= new
        frontier = new
    return sorted(B)

def words(alphabet, n):
    """First n distinct reduced words over alphabet, by length (BFS)."""
    out, seen, layer = [""], {""}, [""]
    while len(out) < n:
        nxt = []
        for w in layer:
            for c in alphabet:
                x = reduce_word(w + c)
                if x not in seen:
                    seen.add(x)
                    nxt.append(x)
                    out.append(x)
        layer = nxt
    return out[:n]

def run(name, S, R, alphaH, alphaK, n):
    B = ball(S, R)
    X = [(w, "") for w in words(alphaH, n)]
    Y = [("", w) for w in words(alphaK, n)]
    core = {mul(x, y) for x in X for y in Y}
    C1 = {mul(mul(x, inv(h)), inv(x)) for x in X for h in B}
    C2 = {mul(mul(y, h), mul(inv(y), inv(h))) for y in Y for h in B}
    A = core | C1 | C2
    Aset = A
    def good(a):
        ai = inv(a)
        for h in B:
            g = mul(mul(a, h), ai)
            if all(mul(g, v) not in Aset for v in A):
                return True
        return False
    bad_core = sum(1 for a in core if not good(a))
    ngood = sum(1 for a in A if good(a))
    print(f"{name}: R={R} #B(R)={len(B)} n={n} #core={len(core)} "
          f"#A={len(A)} core_bad={bad_core}/{len(core)} #good={ngood} "
          f"#A/2={len(A)/2:.1f} SF_fails={ngood < len(A)/2}")
    assert bad_core == len(core)
    assert ngood < len(A) / 2

if __name__ == "__main__":
    ab = "aAbB"
    prod = [("a", ""), ("A", ""), ("b", ""), ("B", ""),
            ("", "a"), ("", "A"), ("", "b"), ("", "B")]
    run("F2xF2 product gens", prod, 1, ab, ab, 20)
    run("F2xF2 product gens, larger n", prod, 1, ab, ab, 40)
    mixed = [("a", "a"), ("A", "A"), ("b", ""), ("B", ""),
             ("", "b"), ("", "B"), ("ab", "B"), ("BA", "b")]
    run("F2xF2 mixed gens", mixed, 1, ab, ab, 20)
    dinf = [("a", ""), ("A", ""), ("b", ""), ("B", ""),
            ("", "s"), ("", "t"), ("a", "s"), ("A", "s")]
    run("F2xDinf mixed gens", dinf, 1, ab, "st", 20)
    run("F2xZ product gens", [("a", ""), ("A", ""), ("b", ""), ("B", ""),
                              ("", "c"), ("", "C")], 1, ab, "cC", 16)
    print("all assertions passed")
