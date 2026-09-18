#!/usr/bin/env python3
"""Discharging lower bound for S(n -> k) on caterpillar and vine tuples (rigorous, all degrees N).

Class C in {cat, vine}: cat = trees in which every caret has a leaf child; vine = left or right vines.
Both are closed under taking subtrees.  For u in T^k put deg(u) = #{s in S : u = s(b), b in C^n}
(each s is injective, so each s gives at most one b).  Discharging: every a in A subset C^n sends
1/deg(s a) to each image s a.  An image receives at most deg(u) * (1/deg(u)) = 1, hence

    |S A| >= sum_(a in A) phi(a),   phi(a) = sum_(s in S) 1/deg(s a)

(an image u is hit by at most deg(u) pairs (a, s) with s a = u, since each s has at most one
preimage of u), 
so |S A| / |A| >= min phi over C^n.  phi(a) depends only on the type vector of a, where the type
of a tree is leaf / (leaf,leaf) / (nonleaf,leaf) / (leaf,nonleaf) (see the node for the argument), and
is checked here (1) by evaluating phi on type representatives, (2) by checking that phi is constant
on type classes over all tuples with N <= NMAX carets.
"""
import itertools, sys, collections
from fractions import Fraction as Fr
import skeleton as sk

LEAF = 0
REPS = [LEAF, (LEAF, LEAF), ((LEAF, LEAF), LEAF), (LEAF, (LEAF, LEAF))]


def is_L(t):
    while t != LEAF:
        if t[1] != LEAF:
            return False
        t = t[0]
    return True


def is_R(t):
    while t != LEAF:
        if t[0] != LEAF:
            return False
        t = t[1]
    return True


def in_class(cls, t):
    if cls == 'vine':
        return is_L(t) or is_R(t)
    if cls == 'cat':
        return t == LEAF or ((t[0] == LEAF or t[1] == LEAF) and in_class(cls, t[0]) and in_class(cls, t[1]))
    raise ValueError(cls)


def tau(t):
    if t == LEAF:
        return 0
    if t[0] == LEAF and t[1] == LEAF:
        return 1
    if t[1] == LEAF:
        return 2
    if t[0] == LEAF:
        return 3
    return 4  # not in either class


def match(sym, t, b):
    """Try to write t as the symbolic forest entry sym; fill b[leaf index] = piece."""
    if isinstance(sym, int):
        b[sym] = t
        return True
    if t == LEAF:
        return False
    return match(sym[0], t[0], b) and match(sym[1], t[1], b)


def preimage(s, u, n):
    b = [None] * n
    for sym, t in zip(s, u):
        if not match(sym, t, b):
            return None
    return tuple(b)


def deg(cls, maps, u, n):
    c = 0
    for s in maps:
        b = preimage(s, u, n)
        if b is not None and all(in_class(cls, x) for x in b):
            c += 1
    return c


def phi(cls, maps, a):
    n = len(a)
    imgs = [tuple(sk.instantiate(x, a) for x in s) for s in maps]
    return sum(Fr(1, deg(cls, maps, u, n)) for u in imgs)


def run(cls, n, k, nmax):
    maps = sk.merge_maps(n, k)
    reps = [r for r in REPS if in_class(cls, r)]
    by_type = {}
    for combo in itertools.product(range(len(reps)), repeat=n):
        a = tuple(reps[i] for i in combo)
        by_type[tuple(tau(x) for x in a)] = phi(cls, maps, a)
    worst = min(by_type.values())
    arg = [t for t, v in by_type.items() if v == worst]
    # consistency: phi is a function of the type vector on all tuples with <= nmax carets
    checked = 0
    for N in range(nmax + 1):
        for a in sk.universe(n, N, cls):
            assert phi(cls, maps, a) == by_type[tuple(tau(x) for x in a)], a
            checked += 1
    print(f"S({n}->{k}) class={cls}: min phi = {worst} ~{float(worst):.6f} at types {arg[:4]}"
          f" ({len(arg)} minimisers); type-determinacy checked on {checked} tuples (N<={nmax})", flush=True)
    return worst


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for cls in ('cat', 'vine'):
        for n, k in ((3, 2), (4, 3), (4, 2), (5, 3), (6, 4)):  # d <= 2 only: types see depth <= 2
            run(cls, n, k, nmax if n <= 5 else max(3, nmax - 2))
