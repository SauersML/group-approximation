#!/usr/bin/env python3
"""Independent checks for ore_linalg.py / ore_certify.py.

(1) The normal-form routine agrees with the faithful action of F on [0,1] by piecewise-linear
    homeomorphisms: for every word w in the tested range, the PL map of w equals the PL map of
    normalize(w), and distinct normal forms give distinct PL maps.
(2) Explicit certificates a u = b v are rechecked by composing PL maps, never using normal forms.

Usage: ore_verify.py nf MAXLEN MAXLETTER
       ore_verify.py cert CERT.json
"""
import itertools, json, random, sys
from fractions import Fraction as Q


def canon(points):
    """Drop breakpoints where the slope does not change."""
    pts = [points[0]]
    for p in points[1:]:
        if len(pts) >= 2:
            (x0, y0), (x1, y1) = pts[-2], pts[-1]
            if (y1 - y0) * (p[0] - x1) == (p[1] - y1) * (x1 - x0):
                pts[-1] = p
                continue
        pts.append(p)
    return tuple(pts)


def evaluate(pts, x):
    for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
        if x0 <= x <= x1:
            return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
    raise ValueError(x)


def inverse_eval(pts, y):
    return evaluate(tuple((b, a) for a, b in pts), y)


def compose(g, f):
    """Return the PL map g o f (apply f first)."""
    xs = {p[0] for p in f}
    xs |= {inverse_eval(f, p[0]) for p in g}
    xs = sorted(xs)
    return canon([(x, evaluate(g, evaluate(f, x))) for x in xs])


def gen(n):
    c = 1 - Q(1, 2 ** n)
    L = Q(1, 2 ** n)
    pts = [(Q(0), Q(0))]
    if n > 0:
        pts.append((c, c))
    pts += [(c + L / 2, c + L / 4), (c + 3 * L / 4, c + L / 2), (Q(1), Q(1))]
    return canon(pts)


IDENT = canon([(Q(0), Q(0)), (Q(1), Q(1))])
_GEN = {}


def g_(n):
    if n not in _GEN:
        _GEN[n] = gen(n)
    return _GEN[n]


def word_map(w, order):
    """order 'lr': x_{i1} is applied first; 'rl': x_{id} is applied first."""
    m = IDENT
    seq = w if order == "lr" else tuple(reversed(w))
    for i in seq:
        m = compose(g_(i), m)
    return m


def normalize(w):
    w = list(w)
    changed = True
    while changed:
        changed = False
        for k in range(len(w) - 1):
            if w[k] > w[k + 1]:
                j, i = w[k], w[k + 1]
                w[k], w[k + 1] = i, j + 1
                changed = True
    return tuple(w)


def pick_order():
    ok = []
    for order in ("lr", "rl"):
        good = all(word_map((j, i), order) == word_map((i, j + 1), order)
                   for i in range(4) for j in range(i + 1, 5))
        if good:
            ok.append(order)
    assert len(ok) == 1, ok
    return ok[0]


def check_nf(maxlen, maxletter):
    order = pick_order()
    seen = {}
    nwords = 0
    for L in range(1, maxlen + 1):
        for w in itertools.product(range(maxletter + 1), repeat=L):
            nf = normalize(w)
            m = word_map(w, order)
            m2 = word_map(nf, order)
            assert m == m2, (w, nf)
            prev = seen.get(m)
            assert prev is None or prev == nf, (w, nf, prev)
            seen[m] = nf
            nwords += 1
    rnd = random.Random(20260913)
    for _ in range(3000):
        L = rnd.randint(7, 11)
        w = tuple(rnd.randint(0, 8) for _ in range(L))
        assert word_map(w, order) == word_map(normalize(w), order), w
    print(json.dumps({"order": order, "words_checked": nwords, "distinct_maps": len(seen),
                      "random_long_words": 3000, "ALL_OK": True}))


def check_cert(path):
    order = pick_order()
    with open(path) as f:
        certs = json.load(f)
    nok = 0
    for c in certs:
        S = [tuple(s) for s in c["S"]]
        a = [S[i] for i in range(len(S)) if c["a"] >> i & 1]
        b = [S[i] for i in range(len(S)) if c["b"] >> i & 1]
        u = [tuple(x) for x in c["u"]]
        v = [tuple(x) for x in c["v"]]
        assert u and v
        lhs, rhs = {}, {}
        for s in a:
            for x in u:
                m = word_map(s + x, order)
                lhs[m] = lhs.get(m, 0) ^ 1
        for s in b:
            for x in v:
                m = word_map(s + x, order)
                rhs[m] = rhs.get(m, 0) ^ 1
        L = {m for m, e in lhs.items() if e}
        R = {m for m, e in rhs.items() if e}
        assert L == R and L, (c["a"], c["b"])
        nok += 1
    print(json.dumps({"certificates_checked": nok, "ALL_OK": True}))


if __name__ == "__main__":
    if sys.argv[1] == "nf":
        check_nf(int(sys.argv[2]), int(sys.argv[3]))
    else:
        check_cert(sys.argv[2])
