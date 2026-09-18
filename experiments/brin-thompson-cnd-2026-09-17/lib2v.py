"""Exact arithmetic for the Brin-Thompson group 2V acting on C^2 = {0,1}^N x {0,1}^N.

An element is a finite tuple of brick maps (dx, dy, rx, ry) of binary strings meaning
    (dx + s, dy + t)  |->  (rx + s, ry + t)
on the brick [dx] x [dy]; the domain bricks partition C^2 and so do the range bricks.

Main functions
  compose(g, h)      : the element g o h (apply h first)
  inverse(g)
  canon(g, u, v)     : (U, V) if g restricted to the brick [u] x [v] is the single brick map
                       (u s, v t) -> (U s, V t); otherwise None
  min_bricks(g)      : the minimal number of bricks in a brick diagram of g (exact; uses the
                       guillotine lemma: every partition of a dyadic brick into dyadic bricks
                       has a midline cut, and x-splits are only useful where the diagram is x-finer)
  is_identity(g)
  exponent_profile(g): list of (area, ax, ay) with ax = |rx|-|dx|, ay = |ry|-|dy| over bricks
"""
from fractions import Fraction
from functools import lru_cache
import random

ID = (("", "", "", ""),)


def _cmp(a, b):
    """True if one of a, b is a prefix of the other."""
    n = min(len(a), len(b))
    return a[:n] == b[:n]


def check(g):
    """Verify that domains and ranges are partitions (area 1, pairwise disjoint)."""
    area_d = sum(Fraction(1, 2 ** (len(b[0]) + len(b[1]))) for b in g)
    area_r = sum(Fraction(1, 2 ** (len(b[2]) + len(b[3]))) for b in g)
    assert area_d == 1 and area_r == 1, (area_d, area_r)
    for i in range(len(g)):
        for j in range(i + 1, len(g)):
            a, b = g[i], g[j]
            assert not (_cmp(a[0], b[0]) and _cmp(a[1], b[1])), ("dom overlap", a, b)
            assert not (_cmp(a[2], b[2]) and _cmp(a[3], b[3])), ("rng overlap", a, b)
    return True


def inverse(g):
    return tuple((rx, ry, dx, dy) for (dx, dy, rx, ry) in g)


def compose(g, h):
    """g o h."""
    out = []
    for (hdx, hdy, hrx, hry) in h:
        for (gdx, gdy, grx, gry) in g:
            if not (_cmp(hrx, gdx) and _cmp(hry, gdy)):
                continue
            ix = hrx if len(hrx) >= len(gdx) else gdx
            iy = hry if len(hry) >= len(gdy) else gdy
            # pull back through h, push through g
            dx = hdx + ix[len(hrx):]
            dy = hdy + iy[len(hry):]
            rx = grx + ix[len(gdx):]
            ry = gry + iy[len(gdy):]
            out.append((dx, dy, rx, ry))
    return tuple(out)


def evaluate(g, x, y):
    """Image of a point given by long enough finite prefixes (x, y)."""
    for (dx, dy, rx, ry) in g:
        if x.startswith(dx) and y.startswith(dy):
            return rx + x[len(dx):], ry + y[len(dy):]
    raise ValueError("prefix too short")


class Diagram:
    """Index for canonical-brick queries on one element."""

    def __init__(self, g):
        self.g = g
        self._canon = {}
        self._cost = {}

    def meeting(self, u, v):
        return [b for b in self.g if _cmp(b[0], u) and _cmp(b[1], v)]

    def canon(self, u, v):
        key = (u, v)
        if key in self._canon:
            return self._canon[key]
        bs = self.meeting(u, v)
        res = None
        if len(bs) == 1 and len(bs[0][0]) <= len(u) and len(bs[0][1]) <= len(v):
            dx, dy, rx, ry = bs[0]
            res = (rx + u[len(dx):], ry + v[len(dy):])
        else:
            finer_x = any(len(b[0]) > len(u) for b in bs)
            if finer_x:
                c0 = self.canon(u + "0", v)
                c1 = c0 and self.canon(u + "1", v)
                if c0 and c1 and c0[1] == c1[1] and c0[0][-1:] == "0" and c1[0][-1:] == "1" \
                        and c0[0][:-1] == c1[0][:-1]:
                    res = (c0[0][:-1], c0[1])
            else:
                c0 = self.canon(u, v + "0")
                c1 = c0 and self.canon(u, v + "1")
                if c0 and c1 and c0[0] == c1[0] and c0[1][-1:] == "0" and c1[1][-1:] == "1" \
                        and c0[1][:-1] == c1[1][:-1]:
                    res = (c0[0], c0[1][:-1])
        self._canon[key] = res
        return res

    def cost(self, u="", v=""):
        key = (u, v)
        if key in self._cost:
            return self._cost[key]
        if self.canon(u, v) is not None:
            self._cost[key] = 1
            return 1
        bs = self.meeting(u, v)
        best = None
        if any(len(b[0]) > len(u) for b in bs):
            best = self.cost(u + "0", v) + self.cost(u + "1", v)
        if any(len(b[1]) > len(v) for b in bs):
            c = self.cost(u, v + "0") + self.cost(u, v + "1")
            best = c if best is None else min(best, c)
        self._cost[key] = best
        return best


def min_bricks(g):
    return Diagram(g).cost()


def is_identity(g):
    return Diagram(g).canon("", "") == ("", "")


def reduce_greedy(g):
    """Merge sibling brick pairs until none merges; returns an equal element (not nec. minimal)."""
    bricks = set(g)
    changed = True
    while changed:
        changed = False
        idx = {}
        for b in bricks:
            idx[(b[0], b[1])] = b
        for b in list(bricks):
            if b not in bricks:
                continue
            dx, dy, rx, ry = b
            for axis in (0, 1):
                d = dx if axis == 0 else dy
                if not d or d[-1] != "0":
                    continue
                sib_key = (dx[:-1] + "1", dy) if axis == 0 else (dx, dy[:-1] + "1")
                s = idx.get(sib_key)
                if s is None or s not in bricks:
                    continue
                r = rx if axis == 0 else ry
                rs = s[2] if axis == 0 else s[3]
                other_ok = (ry == s[3]) if axis == 0 else (rx == s[2])
                if other_ok and r and rs and r[-1] == "0" and rs[-1] == "1" and r[:-1] == rs[:-1]:
                    bricks.discard(b)
                    bricks.discard(s)
                    if axis == 0:
                        nb = (dx[:-1], dy, rx[:-1], ry)
                    else:
                        nb = (dx, dy[:-1], rx, ry[:-1])
                    bricks.add(nb)
                    idx[(nb[0], nb[1])] = nb
                    changed = True
                    break
    return tuple(sorted(bricks))


def exponent_profile(g):
    return [(Fraction(1, 2 ** (len(dx) + len(dy))), len(rx) - len(dx), len(ry) - len(dy))
            for (dx, dy, rx, ry) in g]


# ---------------------------------------------------------------- generators

def v_on_x(pairs):
    """Embed a V element given as list of (domain word, range word) into 2V acting on x."""
    return tuple((d, "", r, "") for d, r in pairs)


def v_on_y(pairs):
    return tuple(("", d, "", r) for d, r in pairs)


# Thompson F generators x0, x1 and a transposition of V
X0 = [("0", "00"), ("10", "01"), ("11", "1")]
X1 = [("0", "0"), ("10", "100"), ("110", "101"), ("111", "11")]
C0 = [("0", "1"), ("1", "0")]            # swap first letter
C1 = [("0", "0"), ("10", "11"), ("11", "10")]
PI = [("0", "10"), ("10", "0"), ("11", "11")]

BAKER = (("0", "", "", "0"), ("1", "", "", "1"))   # (a s, t) -> (s, a t)

GENS_2V = {
    "x0x": v_on_x(X0), "x1x": v_on_x(X1), "c0x": v_on_x(C0), "c1x": v_on_x(C1), "pix": v_on_x(PI),
    "x0y": v_on_y(X0), "x1y": v_on_y(X1), "c0y": v_on_y(C0), "c1y": v_on_y(C1), "piy": v_on_y(PI),
    "bak": BAKER,
}


def word_element(word, gens=GENS_2V):
    g = ID
    for letter in word:
        inv = letter.endswith("'")
        e = gens[letter.rstrip("'")]
        if inv:
            e = inverse(e)
        g = reduce_greedy(compose(g, e))
    return g


def random_word(length, rng, letters=None):
    letters = letters or list(GENS_2V)
    return [rng.choice(letters) + rng.choice(["", "'"]) for _ in range(length)]


if __name__ == "__main__":
    rng = random.Random(1)
    for name, e in GENS_2V.items():
        check(e)
        assert is_identity(compose(e, inverse(e)))
    for _ in range(200):
        w = random_word(rng.randint(1, 8), rng)
        g = word_element(w)
        check(g)
        h = word_element(random_word(rng.randint(1, 8), rng))
        gh = compose(g, h)
        check(gh)
        assert is_identity(compose(gh, inverse(gh)))
        assert min_bricks(g) <= len(reduce_greedy(g))
        # random point test of composition
        x = "".join(rng.choice("01") for _ in range(60))
        y = "".join(rng.choice("01") for _ in range(60))
        a = evaluate(g, *evaluate(h, x, y))
        b = evaluate(gh, x, y)
        n = 20
        assert a[0][:n] == b[0][:n] and a[1][:n] == b[1][:n]
    # V control: min_bricks on V x 1 equals the number of leaves of the reduced tree pair
    assert min_bricks(v_on_x(X0)) == 3 and min_bricks(v_on_x(X1)) == 4
    assert min_bricks(BAKER) == 2
    print("lib2v self-test ok")
