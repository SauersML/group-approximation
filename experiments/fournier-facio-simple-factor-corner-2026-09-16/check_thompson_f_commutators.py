"""Exact check of the elements used in Theorem 5 of
research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md.

For eta = n(n+1), n = 2..6, build the PL maps f, u = f o f, v_1, v_2 of [0,1],
the commutators k_i = u^-1 o v_i o u o v_i^-1, and check with rational
arithmetic:
  * every map has slopes in eta^Z and breakpoints in Z[1/eta];
  * supp k_1 = (eta^-3, 2 eta^-2) + (1/eta, 2/eta);
  * supp k_2 = (eta^-2, 2 eta^-2) + (2/eta - eta^-2, 2/eta);
  * the support of <k_1, k_2> has the two components claimed.
Composition is (g o h)(x) = g(h(x)). Single-threaded, a few ms.
"""
from fractions import Fraction as Fr


class PL:
    def __init__(self, pts):
        # pts: list of (x, y), x strictly increasing from 0 to 1
        self.pts = [(Fr(x), Fr(y)) for x, y in pts]

    def __call__(self, x):
        x = Fr(x)
        for (x0, y0), (x1, y1) in zip(self.pts, self.pts[1:]):
            if x0 <= x <= x1:
                return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
        raise ValueError(x)

    def inv(self):
        return PL([(y, x) for x, y in self.pts])

    def breaks(self):
        return [x for x, _ in self.pts]


def compose(g, h):
    xs = set(h.breaks()) | {h.inv()(x) for x in g.breaks()}
    xs = sorted(xs)
    return PL([(x, g(h(x))) for x in xs])


def slopes(g):
    return [(y1 - y0) / (x1 - x0) for (x0, y0), (x1, y1) in zip(g.pts, g.pts[1:])]


def is_power(q, eta):
    if q <= 0:
        return False
    while q.denominator % eta == 0 and q.numerator % eta != 0:
        q *= eta
    while q.numerator % eta == 0 and q.denominator % eta != 0:
        q /= eta
    return q == 1


def in_ring(q, eta):
    d = q.denominator
    while d % eta == 0:
        d //= eta
    # Z[1/eta]: denominator divides a power of eta
    g = eta
    while d > 1:
        from math import gcd
        c = gcd(d, eta)
        if c == 1:
            return False
        d //= c
    return True


def support(g):
    """Moved set of g as a list of maximal open intervals."""
    xs = g.breaks()
    comps = []
    cur = None
    for x0, x1 in zip(xs, xs[1:]):
        d0, d1 = g(x0) - x0, g(x1) - x1
        moved = not (d0 == 0 and d1 == 0)
        if moved and d0 * d1 < 0:
            raise AssertionError("sign change: not a single bump piece")
        if moved:
            if cur is None:
                cur = [x0, x1]
            elif cur[1] == x0 and d0 != 0:
                cur[1] = x1
            else:
                comps.append(tuple(cur))
                cur = [x0, x1]
        else:
            if cur is not None:
                comps.append(tuple(cur))
                cur = None
    if cur is not None:
        comps.append(tuple(cur))
    return comps


def union(intervals):
    ivs = sorted(intervals)
    out = []
    for a, b in ivs:
        if out and a < out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def bump(eta, p, m):
    s = Fr(1, eta ** m)
    e = Fr(1, eta)
    pts = [(0, 0)] if p > 0 else []
    pts += [(p, p), (p + s * e * e, p + s * e), (p + s * (1 - e), p + s * (1 - e * e)), (p + s, p + s)]
    if p + s < 1:
        pts.append((1, 1))
    return PL(pts)


def run(n):
    eta = n * (n + 1)
    e = Fr(1, eta)
    f = bump(eta, Fr(0), 0)
    u = compose(f, f)
    ui = u.inv()
    v1 = bump(eta, e, 1)
    v2 = bump(eta, 2 * e - e * e, 2)
    k = []
    for v in (v1, v2):
        k.append(compose(compose(compose(ui, v), u), v.inv()))
    for name, g in [("f", f), ("u", u), ("v1", v1), ("v2", v2), ("k1", k[0]), ("k2", k[1])]:
        assert all(is_power(q, eta) for q in slopes(g)), (n, name, slopes(g))
        assert all(in_ring(x, eta) for x in g.breaks()), (n, name)
        assert all(in_ring(y, eta) for _, y in g.pts), (n, name)
    assert f.pts == [(0, 0), (e * e, e), (1 - e, 1 - e * e), (1, 1)]
    assert all(f(x) > x for x in [Fr(j, 997) for j in range(1, 997)])
    assert ui(e) == e ** 3 and ui(2 * e) == 2 * e * e and ui(2 * e - e * e) == e * e
    assert support(v1) == [(e, 2 * e)]
    assert support(v2) == [(2 * e - e * e, 2 * e)]
    s1 = support(k[0])
    s2 = support(k[1])
    assert s1 == [(e ** 3, 2 * e * e), (e, 2 * e)], s1
    assert s2 == [(e * e, 2 * e * e), (2 * e - e * e, 2 * e)], s2
    sQ = union(s1 + s2)
    assert sQ == [(e ** 3, 2 * e * e), (e, 2 * e)], sQ
    # k2 has an orbital inside (1/eta, 2/eta) ending at 2/eta and none starting at 1/eta
    inside = [B for B in s2 if e <= B[0] and B[1] <= 2 * e]
    assert inside == [(2 * e - e * e, 2 * e)]
    assert any(B[1] == 2 * e for B in inside) and not any(B[0] == e for B in inside)
    return eta, s1, s2, sQ


if __name__ == "__main__":
    for n in range(2, 7):
        eta, s1, s2, sQ = run(n)
        print(f"n={n} eta={eta} supp k1={[(str(a), str(b)) for a, b in s1]} "
              f"supp k2={[(str(a), str(b)) for a, b in s2]} supp Q={[(str(a), str(b)) for a, b in sQ]}")
    print("all checks passed")
