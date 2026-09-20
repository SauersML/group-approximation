#!/usr/bin/env python3
"""Check the invariant lexicographic order on the coset spaces F / Stab(c_p).

For a prime p let c_p(x) = (binary digit sum of x) mod p on the dyadics D of (0,1).
For g in F let g.c = c o g^{-1}.  The claim
`jones-subgroup-coset-spaces-carry-invariant-orders` says:

  (L) the support of g.c - c is the union of the range leaves [.v, .v + 2^-|v|)
      whose tree-pair branch w -> v has ds(w) != ds(v) mod p; the first range
      leaf is never such a leaf, so the support has a least element whenever
      it is nonempty;
  (O) a.c < b.c  iff  at the least point y0 where they differ, a.c(y0) < b.c(y0)
      (as integers in 0..p-1) is a strict total order on F.c which is invariant
      under left multiplication by F.

This script tests (L) exactly on random tree pairs, and (O) on a dyadic grid
of depth N (all breakpoints of the elements used are of depth < N, which the
script asserts), for p in {2, 3, 5}.  Run: python3 jones_coset_order_check.py
Exit status 0 means every check passed.
"""
import random
import sys
from fractions import Fraction

random.seed(20260920)


def random_tree_leaves(n):
    """Leaves (as binary words) of a uniformly-ish random binary tree with n leaves."""
    leaves = [""]
    while len(leaves) < n:
        i = random.randrange(len(leaves))
        w = leaves.pop(i)
        leaves[i:i] = [w + "0", w + "1"]
    return leaves


def random_element(maxleaves=6):
    n = random.randint(1, maxleaves)
    return (random_tree_leaves(n), random_tree_leaves(n))  # domain leaves -> range leaves


def val(w):
    return Fraction(int(w, 2), 2 ** len(w)) if w else Fraction(0)


def apply(g, x, inverse=False):
    dom, ran = g
    if inverse:
        dom, ran = ran, dom
    for w, v in zip(dom, ran):
        a = val(w)
        if a <= x < a + Fraction(1, 2 ** len(w)):
            return val(v) + (x - a) * Fraction(2 ** len(w), 2 ** len(v))
    raise ValueError(x)


def ds(x):
    # x = m / 2^k with denominator a power of two: digit sum = popcount(m)
    assert x.denominator & (x.denominator - 1) == 0
    return bin(x.numerator).count("1")


def colour(g_list, p, y):
    """(g_1 ... g_k).c evaluated at y, i.e. c(g_k^{-1} ... g_1^{-1} y)."""
    for g in g_list:
        y = apply(g, y, inverse=True)
    return ds(y) % p


def grid(N):
    return [Fraction(m, 2 ** N) for m in range(1, 2 ** N)]


def check_L(p, trials=400):
    for _ in range(trials):
        g = random_element(7)
        dom, ran = g
        mism = [ds(val(w)) % p != ds(val(v)) % p for w, v in zip(dom, ran)]
        assert not mism[0], "first leaf mismatched"
        # exact check on each range leaf, sampling points .v u
        for (w, v), bad in zip(zip(dom, ran), mism):
            for u in ["", "1", "01", "11", "0011", "101"]:
                y = val(v + u)
                if y == 0:
                    continue
                differs = colour([g], p, y) != ds(y) % p
                assert differs == (bad and (ds(val(w)) + ds(val(u))) % p != (ds(val(v)) + ds(val(u))) % p)
                if u == "":
                    # left endpoint of a mismatched leaf is in the support
                    assert differs == bad
        # least element of the support
        predicted = next((val(v) for (w, v), bad in zip(zip(dom, ran), mism) if bad), None)
        N = 12
        pts = [y for y in grid(N) if colour([g], p, y) != ds(y) % p]
        actual = pts[0] if pts else None
        assert predicted == actual, (g, predicted, actual)
    return True


def first_diff(A, B, p, pts):
    for y in pts:
        ca, cb = colour(A, p, y), colour(B, p, y)
        if ca != cb:
            return y, ca, cb
    return None


def less(A, B, p, pts):
    r = first_diff(A, B, p, pts)
    if r is None:
        return None
    return r[1] < r[2]


def check_O(p, trials=150):
    N = 11
    pts = grid(N)
    fine = grid(N + 2)
    n_nontrivial = 0
    for _ in range(trials):
        a, b, f, e = (random_element(4) for _ in range(4))
        A, B, C = [a], [b], [e]
        r = first_diff(A, B, p, pts)
        if r is None:
            continue
        # the first difference on the fine grid is the same point: depth N suffices
        assert first_diff(A, B, p, fine)[0] == r[0]
        n_nontrivial += 1
        l1 = less(A, B, p, pts)
        l2 = less(B, A, p, pts)
        assert l1 is not None and l1 != l2, "antisymmetry"
        # invariance under left multiplication by f: (f a).c = f.(a.c)
        fr = first_diff([f] + A, [f] + B, p, fine)
        assert fr is not None
        assert fr[0] == apply(f, r[0]), "first difference moves by f"
        assert (fr[1], fr[2]) == (r[1], r[2]), "colour pair at first difference is F-invariant"
        # transitivity on triples
        l_bc = less(B, C, p, pts)
        l_ac = less(A, C, p, pts)
        if l1 and l_bc:
            assert l_ac, "transitivity"
    return n_nontrivial


if __name__ == "__main__":
    ok = True
    for p in (2, 3, 5):
        check_L(p)
        n = check_O(p)
        print(f"p={p}: (L) exact leaf test passed; (O) passed on {n} nontrivial random pairs")
    sys.exit(0)
