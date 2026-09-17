#!/usr/bin/env python3
"""verify_chain.py -- independent check of a pzsearch GOAL chain.

usage: pzsearch RANK CAP MAX r1 r2 | verify_chain.py RANK r1 r2

Checks, with code independent of pzsearch.c:
  1. the first chain state equals (r1, r2) up to cyclic rotation, inversion, order and a signed
     permutation of the generators (moves P2 / conjugations);
  2. each consecutive pair of states is related by one move: an automorphism of type 2 or a signed
     permutation applied to both relators (P2), or  r_i -> U g V g^-1  with U a rotation of r_i,
     V a rotation of r_j^{+-1}, g empty or a letter (a P1 composite), all up to rotation / inversion;
  3. some relator of the last state is primitive (explicit Whitehead descent to length 1, printed).
By research/one-stabilization-primitive-relator-criterion-proof.md this certifies that the
one-stabilization of <x,y | r1, r2> is AC-trivial (if <x,y | r1, r2> presents the trivial group).
"""
import itertools
import sys

LET = "xyz"


def inv(w):
    return "".join(c.swapcase() for c in reversed(w))


def red(w):
    out = []
    for c in w:
        if out and out[-1] == c.swapcase():
            out.pop()
        else:
            out.append(c)
    return "".join(out)


def cyc(w):
    w = red(w)
    while len(w) > 1 and w[0] == w[-1].swapcase():
        w = w[1:-1]
    return w


def cform(w):
    """canonical cyclic word up to rotation and inversion (any fixed total order is fine)"""
    w = cyc(w)
    if not w:
        return w
    cands = [w[i:] + w[:i] for i in range(len(w))]
    wi = inv(w)
    cands += [wi[i:] + wi[:i] for i in range(len(wi))]
    return min(cands)


def pform(p, q):
    return tuple(sorted((cform(p), cform(q))))


def subst(w, img):
    return red("".join(img[c] if c.islower() else inv(img[c.lower()]) for c in w))


def signed_perms(rank):
    gens = LET[:rank]
    for perm in itertools.permutations(gens):
        for signs in itertools.product((0, 1), repeat=rank):
            img = {}
            for g, h, s in zip(gens, perm, signs):
                img[g] = h.upper() if s else h
            yield img


def whitehead2(rank):
    gens = LET[:rank]
    for a in gens + gens.upper():
        others = [g for g in gens if g != a.lower()]
        for opts in itertools.product(range(4), repeat=len(others)):
            if not any(opts):
                continue
            img = {g: g for g in gens}
            for g, o in zip(others, opts):
                img[g] = (inv(a) if o in (2, 3) else "") + g + (a if o in (1, 3) else "")
            yield img


def sym_class(p, q, rank):
    return {pform(subst(p, s), subst(q, s)) for s in signed_perms(rank)}


def neighbours(p, q, rank):
    out = set()
    for img in list(whitehead2(rank)) + list(signed_perms(rank)):
        out.add(pform(subst(p, img), subst(q, img)))
    letters = [""] + list(LET[:rank]) + list(LET[:rank].upper())
    for (ri, rj) in ((p, q), (q, p)):
        for V0 in (rj, inv(rj)):
            for a in range(len(ri)):
                U = ri[a:] + ri[:a]
                for b in range(len(V0)):
                    V = V0[b:] + V0[:b]
                    for g in letters:
                        out.add(pform(cyc(U + g + V + inv(g)), rj))
    return out


def is_primitive(w, rank, trace):
    w = cyc(w)
    while len(w) > 1:
        for img in whitehead2(rank):
            v = cyc(subst(w, img))
            if len(v) < len(w):
                trace.append((w, img, v))
                w = v
                break
        else:
            return False
    return len(w) == 1


def main():
    rank = int(sys.argv[1])
    r1, r2 = sys.argv[2], sys.argv[3]
    chain = []
    reading = False
    for line in sys.stdin:
        if line.startswith("CHAIN"):
            reading = True
            continue
        if reading and line.startswith("  "):
            chain.append(tuple(line.split()))
    assert chain, "no chain in input"
    start = pform(r1, r2)
    assert pform(*chain[0]) in sym_class(r1, r2, rank) or pform(*chain[0]) == start, "start mismatch"
    for k in range(len(chain) - 1):
        p, q = chain[k]
        nxt = chain[k + 1]
        target = sym_class(nxt[0], nxt[1], rank)
        nb = neighbours(p, q, rank)
        assert nb & target, f"step {k} not a single move: {chain[k]} -> {nxt}"
        print(f"step {k}: {p} {q} -> {nxt[0]} {nxt[1]} OK")
    last = chain[-1]
    for w in last:
        trace = []
        if is_primitive(w, rank, trace):
            for (u, img, v) in trace:
                print(f"  Whitehead {img}: {u} -> {v}")
            print(f"PRIMITIVE relator {w}; certificate VERIFIED")
            return 0
    print("last state has no primitive relator: FAILED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
