#!/usr/bin/env python3
"""Exact arithmetic for Thompson's group F in two independent representations,
plus a cross-check between them.

Representation 1 (PL): a piecewise linear homeomorphism of [0,1] with dyadic
breakpoints and slopes powers of 2, stored by its minimal breakpoint lists as
integers scaled by 2^K.  This code is copied from
`experiments/thompson-f/cogrowth_exact.py` (this repository, wave 2026-09-17),
whose counts agree with Elvey Price--Guttmann to word length 30.

Representation 2 (tree pairs): the reduced pair (D, R) of finite binary trees,
with the map sending the i-th standard dyadic leaf interval of D affinely onto
the i-th leaf interval of R.  A tree is `None` (leaf) or a pair (left, right).
The preorder bit string of a binary tree is self-delimiting, so a pair of trees
is packed into one Python int, which is the canonical key used by the ball
search: two elements of F are equal iff their keys are equal.

`selftest()` checks: the two F relators are trivial; x0, x1 do not commute;
conversion PL <-> tree pair is a round trip; and for 20000 random words the
tree-pair product and the PL product agree, in both directions of the
conversion.  Word-length-<=8 closed-walk counts are also recomputed in the tree
representation and compared with the published cogrowth terms 1, 4, 28, 232, 2092.
"""
import bisect
import random
import sys

K = 64
ONE = 1 << K

# ---------------------------------------------------------------- PL maps ---


def dy(p, q):
    assert q & (q - 1) == 0 and (p * ONE) % q == 0
    return p * ONE // q


def canon(pts):
    out = [pts[0]]
    for i in range(1, len(pts) - 1):
        x0, y0 = out[-1]
        x1, y1 = pts[i]
        x2, y2 = pts[i + 1]
        if (y1 - y0) * (x2 - x1) != (y2 - y1) * (x1 - x0):
            out.append((x1, y1))
    out.append(pts[-1])
    return (tuple(p[0] for p in out), tuple(p[1] for p in out))


def make(points):
    xs = tuple(dy(*a) for a, _ in points)
    ys = tuple(dy(*b) for _, b in points)
    return canon(list(zip(xs, ys)))


def ev(f, x):
    xs, ys = f
    i = bisect.bisect_right(xs, x) - 1
    if i >= len(xs) - 1:
        assert x == ONE
        return ONE
    num = (x - xs[i]) * (ys[i + 1] - ys[i])
    q, r = divmod(num, xs[i + 1] - xs[i])
    if r:
        raise ArithmeticError("dyadic depth exceeds K")
    return ys[i] + q


def inv(f):
    return (f[1], f[0])


def comp(f, g):
    """f o g : apply g first."""
    gi = inv(g)
    cand = set(g[0])
    for x in f[0]:
        cand.add(ev(gi, x))
    xs = sorted(cand)
    return canon([(x, ev(f, ev(g, x))) for x in xs])


IDENT = make([((0, 1), (0, 1)), ((1, 1), (1, 1))])
X0 = make([((0, 1), (0, 1)), ((1, 2), (1, 4)), ((3, 4), (1, 2)), ((1, 1), (1, 1))])
X1 = make([((0, 1), (0, 1)), ((1, 2), (1, 2)), ((3, 4), (5, 8)), ((7, 8), (3, 4)),
           ((1, 1), (1, 1))])
PL_GENS = [X0, inv(X0), X1, inv(X1)]

# ------------------------------------------------------------- tree pairs ---


def _tree_of_interval(f, a, b):
    """Minimal binary tree over the standard dyadic interval [a,b] on whose leaf
    intervals f is affine with standard dyadic image."""
    u, v = ev(f, a), ev(f, b)
    w = v - u
    interior = any(a < x < b for x in f[0])
    if not interior and w & (w - 1) == 0 and u % w == 0:
        return None
    m = (a + b) // 2
    return (_tree_of_interval(f, a, m), _tree_of_interval(f, m, b))


def _leaves(t, a, b, out):
    if t is None:
        out.append((a, b))
    else:
        m = (a + b) // 2
        _leaves(t[0], a, m, out)
        _leaves(t[1], m, b, out)


def pl_to_tree(f):
    """Reduced tree pair (D, R) of the PL map f."""
    d = _tree_of_interval(f, 0, ONE)
    dom = []
    _leaves(d, 0, ONE, dom)
    rng = [(ev(f, a), ev(f, b)) for a, b in dom]
    r = _tree_from_leaves([b - a for a, b in rng])
    return reduce_pair(d, r)


def _tree_from_leaves(widths):
    """The binary tree whose leaf widths, in order, are the given dyadic widths
    summing to ONE."""
    def build(a, b, i):
        if i < len(widths) and widths[i] == b - a:
            return None, i + 1
        m = (a + b) // 2
        l, i = build(a, m, i)
        r, i = build(m, b, i)
        return (l, r), i
    t, i = build(0, ONE, 0)
    assert i == len(widths)
    return t


def tree_to_pl(pair):
    d, r = pair
    dom, rng = [], []
    _leaves(d, 0, ONE, dom)
    _leaves(r, 0, ONE, rng)
    assert len(dom) == len(rng)
    pts = [(dom[i][0], rng[i][0]) for i in range(len(dom))] + [(ONE, ONE)]
    return canon(pts)


def leafcount(t):
    return 1 if t is None else leafcount(t[0]) + leafcount(t[1])


def union(s, t):
    if s is None:
        return t
    if t is None:
        return s
    return (union(s[0], t[0]), union(s[1], t[1]))


def _extras(t, u, out):
    """u contains t; record, per leaf of t in order, the subtree of u hanging there."""
    if t is None:
        out.append(u)
        return
    _extras(t[0], u[0], out)
    _extras(t[1], u[1], out)


def _attach(t, ex, i):
    if t is None:
        s = ex[i[0]]
        i[0] += 1
        return s
    l = _attach(t[0], ex, i)
    r = _attach(t[1], ex, i)
    return (l, r)


def reduce_pair(d, r):
    """Cancel, repeatedly, every caret whose two children are leaves at the same
    pair of leaf positions in both trees."""
    while True:
        common = _caret_positions(d) & _caret_positions(r)
        if not common:
            return (d, r)
        pos = min(common)
        d, r = _contract(d, pos), _contract(r, pos)


def _caret_positions(t):
    """Positions i such that leaves i, i+1 are the two children of one caret."""
    res = []

    def rec(node, start):
        if node is None:
            return start + 1
        if node[0] is None and node[1] is None:
            res.append(start)
            return start + 2
        m = rec(node[0], start)
        return rec(node[1], m)

    rec(t, 0)
    return set(res)


def _contract(t, pos):
    """Contract the leaf-pair caret starting at leaf position pos."""
    def rec(node, start):
        if node is None:
            return node, start + 1
        if node[0] is None and node[1] is None:
            if start == pos:
                return None, start + 2
            return node, start + 2
        l, m = rec(node[0], start)
        r, e = rec(node[1], m)
        return (l, r), e

    t2, _ = rec(t, 0)
    return t2


def tmul(f, g):
    """f * g in the same convention as comp(f, g) = f o g (apply g first)."""
    df, rf = f
    dg, rg = g
    u = union(rg, df)
    ex = []
    _extras(rg, u, ex)
    dg2 = _attach(dg, ex, [0])
    ex = []
    _extras(df, u, ex)
    rf2 = _attach(rf, ex, [0])
    return reduce_pair(dg2, rf2)


def tinv(f):
    return (f[1], f[0])


TIDENT = (None, None)
TX0 = pl_to_tree(X0)
TX1 = pl_to_tree(X1)
TGENS = [TX0, tinv(TX0), TX1, tinv(TX1)]

# ------------------------------------------------------------------ keys ----


def enc_tree(t, bits):
    if t is None:
        bits.append(0)
    else:
        bits.append(1)
        enc_tree(t[0], bits)
        enc_tree(t[1], bits)


def key(pair):
    bits = [1]
    enc_tree(pair[0], bits)
    enc_tree(pair[1], bits)
    v = 0
    for b in bits:
        v = (v << 1) | b
    return v


def _dec(bits, i):
    if bits[i] == 0:
        return None, i + 1
    l, i = _dec(bits, i + 1)
    r, i = _dec(bits, i)
    return (l, r), i


def unkey(v):
    bits = [int(c) for c in bin(v)[3:]]
    d, i = _dec(bits, 0)
    r, i = _dec(bits, i)
    assert i == len(bits)
    return (d, r)


KEY_GENS = [key(g) for g in TGENS]

# ---------------------------------------------------------------- checks ----


def selftest(trials=20000, seed=1):
    rnd = random.Random(seed)
    assert unkey(key(TX0)) == TX0 and unkey(key(TX1)) == TX1
    assert pl_to_tree(IDENT) == TIDENT
    assert tree_to_pl(TX0) == X0 and tree_to_pl(TX1) == X1

    # relators of F: [x0 x1^-1, x0^-1 x1 x0] and [x0 x1^-1, x0^-2 x1 x0^2]
    letters = {0: 0, 1: 1, 2: 2, 3: 3}
    invl = {0: 1, 1: 0, 2: 3, 3: 2}

    def word_pl(w):
        g = IDENT
        for s in w:
            g = comp(g, PL_GENS[s])
        return g

    def word_tree(w):
        g = TIDENT
        for s in w:
            g = tmul(g, TGENS[s])
        return g

    def comm(u, v):
        ui = [invl[s] for s in reversed(u)]
        vi = [invl[s] for s in reversed(v)]
        return ui + vi + u + v

    r1 = comm([0, 3], [1, 2, 0])
    r2 = comm([0, 3], [1, 1, 2, 0, 0])
    assert word_pl(r1) == IDENT and word_tree(r1) == TIDENT
    assert word_pl(r2) == IDENT and word_tree(r2) == TIDENT
    assert word_tree([0, 2]) != word_tree([2, 0])

    # random words: both representations must agree, through both conversions
    for _ in range(trials):
        n = rnd.randrange(1, 13)
        w = [rnd.randrange(4) for _ in range(n)]
        a = word_pl(w)
        b = word_tree(w)
        assert pl_to_tree(a) == b, w
        assert tree_to_pl(b) == a, w

    # cogrowth terms c_1..c_4 (words of length 2,4,6,8) by brute force in trees
    import itertools
    counts = []
    for L in (2, 4, 6, 8):
        c = 0
        for w in itertools.product(range(4), repeat=L):
            if word_tree(w) == TIDENT:
                c += 1
        counts.append(c)
    assert counts == [4, 28, 232, 2092], counts
    return {"relators_trivial": True, "pl_tree_agree_on_random_words": trials,
            "cogrowth_2_4_6_8": counts, "letters": len(letters)}


if __name__ == "__main__":
    import json
    print(json.dumps(selftest(int(sys.argv[1]) if len(sys.argv) > 1 else 20000), indent=1))
