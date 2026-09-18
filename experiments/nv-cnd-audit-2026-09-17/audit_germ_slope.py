"""Mechanism check for `nv-point-germ-groups-embed-in-zn-by-slope`, in 2V.

The route is a pen-and-paper argument with one import (Delorme-Guichardet).  What a
computation can check is that the mechanism it uses is the mechanism 2V actually has:

  1. the slope cocycle s(g,x) = |w| - |w'| is well defined on deep bricks and satisfies
     s(gh,x) = s(g,hx) + s(h,x);
  2. on Stab(x) it is a homomorphism, and s(g,x) = 0 forces g = id on a brick around x
     (item 1, the heart of the claim);
  3. the compression of item 4: if g is canonical on B = [w] with gB = [wu] strictly
     inside B, then g^k z converges to a fixed point p with s(g,p) = -|u| != 0;
  4. item 5's trichotomy: d <= 0 nonzero => every deep brick around the fixed point is
     compressed; saddles (mixed signs) need n >= 2 -- exhibited here in 2V.

It reuses only the independent 2V implementation in audit_brick_lemma.py.

Usage: python3 audit_germ_slope.py
"""
import itertools
import random

import audit_brick_lemma as A


def slope(g, x1, x2, depth):
    """s(g, x) for x = (x1, x2) given by long prefixes, computed on a deep brick."""
    a1, a2 = x1[:depth], x2[:depth]
    b = A.canon(g, a1, a2)
    assert b is not None, "brick not deep enough"
    return (len(a1) - len(b[0]), len(a2) - len(b[1])), b


def random_2v(n=4, rng=random):
    """A random element of 2V built as a product of random baker maps and swaps."""
    g = A.ID
    for _ in range(n):
        w = "".join(rng.choice("01") for _ in range(rng.randint(1, 2)))
        k = rng.choice([-2, -1, 1, 2])
        g = A.compose(g, A.power(A.baker(w), k))
    return g


def check_cocycle(trials=300, seed=5):
    print("1-2. slope cocycle, homomorphism on the stabiliser, zero slope => locally trivial")
    rng = random.Random(seed)
    depth = 9
    bad = 0
    for _ in range(trials):
        g, h = random_2v(3, rng), random_2v(3, rng)
        x1 = "".join(rng.choice("01") for _ in range(depth + 8))
        x2 = "".join(rng.choice("01") for _ in range(depth + 8))
        sh, _ = slope(h, x1, x2, depth)
        y1, y2 = A.apply_point(h, x1, x2)
        sg, _ = slope(g, y1, y2, depth)
        sgh, _ = slope(A.compose(g, h), x1, x2, depth)
        if sgh != (sg[0] + sh[0], sg[1] + sh[1]):
            bad += 1
    print(f"   s(gh,x) = s(g,hx) + s(h,x) on {trials} random (g,h,x): violations {bad}")

    # zero slope at a fixed point forces local triviality
    bad2 = tested = 0
    for _ in range(4000):
        g = random_2v(2, rng)
        a1 = "".join(rng.choice("01") for _ in range(4))
        a2 = "".join(rng.choice("01") for _ in range(4))
        b = A.canon(g, a1, a2)
        if b is None:
            continue
        if (len(a1) - len(b[0]), len(a2) - len(b[1])) == (0, 0) and (b[0], b[1]) == (a1, a2):
            tested += 1
            # g is then the identity on [a1] x [a2]
            for s in ("000", "101"):
                for t in ("011", "110"):
                    if A.apply_point(g, a1 + s, a2 + t) != (a1 + s, a2 + t):
                        bad2 += 1
    print(f"   zero slope with image brick = domain brick => identity there: "
          f"{tested} bricks tested, violations {bad2}")
    return bad + bad2


def check_compression():
    print("3-4. item 4 (a canonical self-compression has a fixed point of nonzero slope)"
          " and item 5")
    # Thompson's x_0 acting in coordinate 1 only: it is canonical on B = [0] x C with
    # image [00] x C, a strict sub-brick.
    x1 = (("0", "", "00", ""), ("10", "", "01", ""), ("11", "", "1", ""))
    # the same in coordinate 2
    x2 = (("", "0", "", "00"), ("", "10", "", "01"), ("", "11", "", "1"))
    both = A.compose(x1, x2)
    for name, g in (("x0 in coordinate 1", x1), ("x0 in both coordinates", both)):
        assert A.is_element(g), name
        found = None
        for d1, d2 in itertools.product(range(4), repeat=2):
            for a1 in map("".join, itertools.product("01", repeat=d1)):
                for a2 in map("".join, itertools.product("01", repeat=d2)):
                    b = A.canon(g, a1, a2)
                    if b is None:
                        continue
                    if b[0].startswith(a1) and b[1].startswith(a2) and (b[0], b[1]) != (a1, a2):
                        found = (a1, a2, b)
                        break
                if found:
                    break
            if found:
                break
        assert found, name
        a1, a2, b = found
        u1, u2 = b[0][len(a1):], b[1][len(a2):]
        p1 = a1 + (u1 * 30 if u1 else "0" * 30)
        p2 = a2 + (u2 * 30 if u2 else "0" * 30)
        q1, q2 = A.apply_point(g, p1, p2)
        fixed = q1.startswith(p1[:20]) and q2.startswith(p2[:20])
        s, _ = slope(g, p1, p2, 12)
        print(f"   {name}: B = [{a1 or 'e'}] x [{a2 or 'e'}], gB = [{b[0] or 'e'}] x "
              f"[{b[1] or 'e'}], u = ({u1!r}, {u2!r})")
        print(f"      p = (prefix {a1}, u1^inf ; prefix {a2}, u2^inf) fixed to depth 20: "
              f"{fixed};  s(g,p) = {s}, item 4 predicts {(-len(u1), -len(u2))}")
        assert fixed and s == (-len(u1), -len(u2))
    return 0


def check_saddle():
    print("5. a saddle (slope with coordinates of both signs) exists in 2V, none in 1V")
    # b_ = baker on the whole space moves one letter from coord 1 to coord 2:
    # on [0] x C the element b = baker("") has slope (+1, -1) at the fixed point (0^inf, 0^inf)?
    g = A.baker("")
    x1, x2 = "0" * 30, "0" * 30
    y1, y2 = A.apply_point(g, x1, x2)
    s, b = slope(g, x1, x2, 6)
    print(f"   b = baker(''), x = (0^inf, 0^inf): g(x) = x to depth 25: "
          f"{y1[:25] == x1[:25] and y2[:25] == x2[:25]}, s(g,x) = {s}")
    print("   coordinates of s have opposite signs: "
          f"{s[0] * s[1] < 0}  -- impossible for n = 1, where Z has a sign")
    return 0


if __name__ == "__main__":
    bad = check_cocycle()
    print()
    check_compression()
    print()
    check_saddle()
    print()
    print("VIOLATIONS:", bad)
