"""Calibration lens for `brin-thompson-nv-max-type-size-functions-are-not-cnd`:
does the obstruction prove too much?

The worry.  1V = Thompson's V has the Haagerup property (Farley), so it carries a
proper cnd function.  If the route's argument applied verbatim to 1V it would be
refuted on the spot.  The route's hypothesis is

    psi(g(w)) / G(||w||_inf) -> kappa > 0,  G regularly varying of index beta >= 1/4,

for a Z^3 of disjoint-support elements, and the route verifies it for psi = log L
using L(g(w)) = 2^{||w||_inf + O(1)}.  So the question is exactly: can leaf/brick
count grow *exponentially* along a cyclic subgroup of 1V?

The answer is no, and the reason is a one-line difference between n = 1 and n >= 2:

    n = 1:  two cylinder partitions of C with a and b pieces have a common
            refinement with at most a + b - 1 pieces (binary trees: the union of a
            tree with a leaves and a tree with b leaves has at most a + b - 1
            leaves).  Hence L(gh) - 1 <= (L(g)-1) + (L(h)-1) and L(x^k) - 1 <=
            k (L(x)-1): leaf count grows at most LINEARLY, so log L(g(w)) =
            O(log ||w||_inf), which is slowly varying (index 0) and is precisely the
            case the claim lists as untouched.

    n >= 2: two brick partitions with a and b pieces refine to as many as a*b
            pieces, and the baker map attains it: L(b_w^k) = 2^k + O(1).

This file checks both halves by exact computation:

  (A) in V: L(x^k) for the elements of V that a search finds most expanding, and the
      subadditivity L(gh) - 1 <= (L(g)-1) + (L(h)-1) on random pairs;
  (B) in V: for three disjoint-support elements the leaf count is additive over the
      pieces, i.e. an l^1 function of them, which is the shape the claim says survives;
  (C) in 2V: the same three-piece construction is l^1 in 2^{|exponent|}, so its log
      is the l^inf norm -- the step that has no 1V analogue.

Usage: python3 audit_calibration_1v.py
"""
import itertools
import random

# ---------------------------------------------------------------- V = 1V
# element: tuple of (u, v) meaning [u] -> [v] by u s |-> v s; domains and ranges
# are each a cylinder partition of C.

VID = (("", ""),)


def vcomparable(a, b):
    n = min(len(a), len(b))
    return a[:n] == b[:n]


def vcheck(g):
    da = sum(2.0 ** -len(u) for u, _ in g)
    ra = sum(2.0 ** -len(v) for _, v in g)
    assert abs(da - 1) < 1e-12 and abs(ra - 1) < 1e-12, (da, ra)
    for i in range(len(g)):
        for j in range(i + 1, len(g)):
            assert not vcomparable(g[i][0], g[j][0])
            assert not vcomparable(g[i][1], g[j][1])
    return True


def vinv(g):
    return tuple((v, u) for u, v in g)


def vcompose(g, h):
    out = []
    for (hu, hv) in h:
        for (gu, gv) in g:
            if not vcomparable(hv, gu):
                continue
            m = hv if len(hv) >= len(gu) else gu
            out.append((hu + m[len(hv):], gv + m[len(gu):]))
    return tuple(out)


def vcanon(g, a):
    """b with g(a s) = b s on [a], or None."""
    b = None
    for (u, v) in g:
        if not vcomparable(u, a):
            continue
        c = a if len(a) >= len(u) else u
        w = v + c[len(u):]
        t = c[len(a):]
        if not w.endswith(t):
            return None
        cand = w[:len(w) - len(t)] if t else w
        if b is None:
            b = cand
        elif b != cand:
            return None
    return b


def vmin_leaves(g):
    """Minimal number of cylinders in a diagram of g (exact; the domain tree is the
    smallest tree all of whose leaves are canonical, which is unique)."""
    def rec(a):
        if vcanon(g, a) is not None:
            return 1
        return rec(a + "0") + rec(a + "1")
    return rec("")


def vpower(g, k):
    if k == 0:
        return VID
    base = g if k > 0 else vinv(g)
    out = base
    for _ in range(abs(k) - 1):
        out = vcompose(out, base)
    return out


def vrandom(depth=3, rng=random):
    """A random element of V: a random tree pair with a random leaf bijection."""
    def tree(d):
        if d == 0 or rng.random() < 0.45:
            return [""]
        return ["0" + x for x in tree(d - 1)] + ["1" + x for x in tree(d - 1)]
    while True:
        A, B = tree(depth), tree(depth)
        if len(A) == len(B):
            break
    rng.shuffle(B)
    return tuple(zip(A, B))


def vshift_on(pref):
    """An infinite-order element supported on [pref]: Thompson's x_0 pushed into
    [pref], i.e. [pref 00] -> [pref 0], [pref 01] -> [pref 10], [pref 1] -> [pref 11]."""
    bricks = [(pref + "00", pref + "0"), (pref + "01", pref + "10"), (pref + "1", pref + "11")]
    for i in range(len(pref)):
        flip = pref[:i] + ("1" if pref[i] == "0" else "0")
        bricks.append((flip, flip))
    return tuple(bricks)


# ---------------------------------------------------------------- checks
def check_A(trials=400, seed=11):
    print("A. V: leaf growth is linear, and L-1 is subadditive")
    rng = random.Random(seed)
    worst = 0
    worst_g = None
    for _ in range(trials):
        g = vrandom(3, rng)
        vcheck(g)
        L1 = vmin_leaves(g)
        prev = L1
        growths = []
        for k in range(1, 9):
            Lk = vmin_leaves(vpower(g, k))
            growths.append(Lk)
        ratio = growths[-1] / max(1, k * (L1 - 1) + 1) if L1 > 1 else 0
        if growths[-1] > worst:
            worst, worst_g = growths[-1], (g, growths, L1)
        # subadditivity on this g against a second random element
        h = vrandom(3, rng)
        assert vmin_leaves(vcompose(g, h)) - 1 <= (vmin_leaves(g) - 1) + (vmin_leaves(h) - 1), \
            "SUBADDITIVITY FAILS"
    g, growths, L1 = worst_g
    print(f"   {trials} random pairs: L(gh)-1 <= (L(g)-1)+(L(h)-1) always holds")
    print(f"   most expanding sampled g has L(g)={L1}; L(g^k), k=1..8: {growths}")
    print(f"   bound k*(L(g)-1)+1, k=1..8: {[k * (L1 - 1) + 1 for k in range(1, 9)]}")
    print("   => log L(g^k) = O(log k): slowly varying (index 0), outside the route's"
          " beta >= 1/4 hypothesis")


def check_B():
    print("B. V: three disjoint-support elements -- the leaf count is ADDITIVE (l^1),\n   so L(g(w)) is LINEAR in ||w||_1 (exceptions below are the degenerate\n   exponent-0 merges, where two identity cylinders fuse into one)")
    x, y, z = vshift_on("00"), vshift_on("01"), vshift_on("1")
    for a, b in ((x, y), (x, z), (y, z)):
        assert vcompose(a, b) == vcompose(b, a) or \
            vmin_leaves(vcompose(vcompose(a, b), vinv(vcompose(b, a)))) == 1, "not commuting"
    def leaves(g):
        """The (unique) minimal domain cylinder diagram of g."""
        out = []

        def rec(a):
            if vcanon(g, a) is not None:
                out.append(a)
            else:
                rec(a + "0")
                rec(a + "1")
        rec("")
        return out

    def cost(elt, pref):
        """Cylinders of the minimal diagram of elt that lie inside [pref]."""
        return sum(1 for a in leaves(elt) if a.startswith(pref)) or 1

    rows = []
    bad = 0
    R = 4
    for m, p, q in itertools.product(range(-R, R + 1), repeat=3):
        g = vcompose(vcompose(vpower(x, m), vpower(y, p)), vpower(z, q))
        L = vmin_leaves(g)
        parts = (cost(vpower(x, m), "00"), cost(vpower(y, p), "01"), cost(vpower(z, q), "1"))
        if L != sum(parts):
            bad += 1
            if bad < 5:
                print(f"   NON-ADDITIVE at {(m, p, q)}: L={L} vs pieces {parts}")
        rows.append(((m, p, q), L, max(abs(m), abs(p), abs(q)), abs(m) + abs(p) + abs(q)))
    n = (2 * R + 1) ** 3
    print(f"   {n} elements g(m,p,q) in V, |exponents| <= {R}: "
          f"L is exactly the SUM of the three local costs in {n - bad}/{n} cases")
    for t in ((1, 1, 1), (2, 2, 2), (3, 3, 3), (4, 4, 4), (4, 0, 0), (0, 0, 4)):
        r = [r for r in rows if r[0] == t][0]
        print(f"      w={t}: L={r[1]}   ||w||_inf={r[2]}  2^||w||_inf={2 ** r[2]}  ||w||_1={r[3]}")
    print("   => log L(g(w)) ~ log ||w||_1: index 0.  l^1 functions of the pieces are"
          " exactly what the claim says survives, and l^1 metrics ARE of negative type.")


def check_C():
    print("C. 2V: the same three-piece construction, but each piece costs 2^|exponent|")
    import audit_brick_lemma as A
    rows = []
    for w in ((1, 1, 1), (2, 2, 2), (3, 0, 0), (0, 0, 3), (2, 0, 3)):
        g = A.g_of(*w)
        d = max(abs(t) for t in w) + 3
        L = A.min_bricks(g, d)[0] if max(abs(t) for t in w) <= 2 else None
        rows.append((w, L, 2 ** max(abs(t) for t in w), sum(2 ** abs(t) for t in w)))
    for w, L, lo, hi in rows:
        print(f"   w={w}: exact L={L}, bounds [{lo}, {hi}]")
    print("   => log L = ||w||_inf log 2 + O(1): index 1 in ||w||_inf.  The n=1 leaf")
    print("      count cannot do this, because a cylinder refinement is a + b - 1, not a*b.")


if __name__ == "__main__":
    check_A()
    print()
    check_B()
    print()
    check_C()
