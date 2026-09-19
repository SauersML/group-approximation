#!/usr/bin/env python3
"""Checks for the group-level orbit trap (no linearity, no Loewy filtration).

d_g(x) = x g x g for involutions g, x.  Lambda_b = d_{x12(b)} d_c,
M_b = d_{x43(b)} d_{b1}.  Z = right d-orbit of u (closure of {u} under
d_b1, d_bs, d_bt).

Part 1. Exhaustive check in S_5 of the identity used in the proof: for
commuting involutions a, b and any z,
    d_a d_b z = d_b d_a z   iff   [b z b, a z a] = 1.
Part 2. The trap words in P_{2,2}(J): the right orbit of u up to depth 4 is
computed exactly over J and lies in the abelian group n(M_2(J)); the
left/right d-maps commute on it; Lambda_t Lambda_s u = u and
Lambda_s Lambda_t u = x_13(ST) != u.  (Z is infinite in P, which is why the
pigeonhole does not fire there.)
Part 3. The function orbit_trap(model) computes Z and the commutation
condition (C) in any finite model given by matrices over F_2; it is used by
loewy3_search to certify that every head-keeping model violates (C).
"""
import itertools
import sys

import trap_group as TG


# ---------- Part 1: permutations ----------
def pmul(p, q):
    return tuple(q[p[i]] for i in range(len(p)))


def pinv(p):
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def d(g, x, mul):
    return mul(mul(mul(x, g), x), g)


def part1():
    n = 5
    G = list(itertools.permutations(range(n)))
    e = tuple(range(n))
    inv = [g for g in G if pmul(g, g) == e and g != e]
    pairs = [(a, b) for a in inv for b in inv if pmul(a, b) == pmul(b, a)]
    checked = 0
    for a, b in pairs:
        for z in G:
            lhs = d(a, d(b, z, pmul), pmul) == d(b, d(a, z, pmul), pmul)
            x = pmul(pmul(b, z), b)
            y = pmul(pmul(a, z), a)
            rhs = pmul(x, y) == pmul(y, x)
            assert lhs == rhs
            checked += 1
    print("part 1: equivalence checked on", checked, "(a,b,z) triples in S_5")
    return True


# ---------- Part 2: exact words in P_{2,2}(J) ----------
def part2(depth=4):
    val = TG.evaluate()
    mul = TG.mat_mul
    I = TG.mat_id()

    def dd(gname, x):
        return d(val[gname], x, mul)

    def is_n(M):
        # block form [[1, Y], [0, 1]]
        for r in range(4):
            for c in range(4):
                if (r < 2 and c < 2) or (r >= 2 and c >= 2):
                    if M[r][c] != (TG.ONE if r == c else TG.ZERO):
                        return False
                if r >= 2 and c < 2 and M[r][c] != TG.ZERO:
                    return False
        return True

    layer = {val["u"]}
    Z = set(layer)
    for _ in range(depth):
        new = set()
        for z in layer:
            for b in TG.RIGHT:
                y = dd(b, z)
                if y not in Z:
                    new.add(y)
        Z |= new
        layer = new
    assert all(is_n(z) for z in Z)
    for z in Z:
        for a in ["c"]:
            for b in TG.RIGHT:
                assert dd(a, dd(b, z)) == dd(b, dd(a, z))
        zc = dd("c", z)
        for a in ["as", "at"]:
            for b in TG.RIGHT:
                assert dd(a, dd(b, zc)) == dd(b, dd(a, zc))
    lam = lambda b, x: dd(b, dd("c", x))
    u = val["u"]
    assert lam("at", lam("as", u)) == u
    assert lam("as", lam("at", u)) == TG.elem(1, 3, TG.ST) != u
    print("part 2: right orbit of u to depth", depth, "has", len(Z),
          "elements, all in n(M_2(J)); left/right d-maps commute on it;"
          " Lambda_t Lambda_s u = u, Lambda_s Lambda_t u = x13(ST) != u")
    return True


# ---------- Part 3: condition (C) in a finite matrix model ----------
def orbit_trap(G, U, mm, eq, key, limit=200000):
    """G: dict of Levi generator matrices, U: unipotent generator.
    Returns (size of Z, list of violations of (C)).  Z is enumerated by
    breadth-first search under the right d-maps."""
    def dd(g, x):
        return mm(x, G[g], x, G[g])

    Z = {key(U): U}
    frontier = [U]
    while frontier:
        nxt = []
        for z in frontier:
            for b in TG.RIGHT:
                y = dd(b, z)
                k = key(y)
                if k not in Z:
                    Z[k] = y
                    nxt.append(y)
        frontier = nxt
        if len(Z) > limit:
            raise RuntimeError("orbit too large")
    bad = []
    for z in Z.values():
        for b in TG.RIGHT:
            if not eq(dd("c", dd(b, z)), dd(b, dd("c", z))):
                bad.append(("c", b))
        zc = dd("c", z)
        for a in ["as", "at"]:
            for b in TG.RIGHT:
                if not eq(dd(a, dd(b, zc)), dd(b, dd(a, zc))):
                    bad.append((a, b))
    return len(Z), bad


if __name__ == "__main__":
    ok = part1() and part2()
    sys.exit(0 if ok else 1)
