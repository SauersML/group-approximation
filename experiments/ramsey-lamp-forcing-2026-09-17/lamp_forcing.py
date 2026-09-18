"""Exact checks for thompson-f-ramsey-radius-is-at-least-exponential.

Thompson's F acts on [0,1] by PL homeomorphisms; product g*y = g o y (apply y first).
Everything is exact (fractions.Fraction).  Checks:
  (1) the generators act on binary expansions as stated in the proof;
  (2) every letter s in {x0, x1, x0^-1, x1^-1} has at most 3 interior breakpoints, each
      with jump log2 y'(t+) - log2 y'(t-) in {-1, +1}; hence |Br(h)| <= 3|h| on a
      sample of words (checked on all words of length <= WORDLEN);
  (3) the cocycle identity c_{gy}(t) = c_y(g^-1 t) + c_g(t), where c_y := beta_{y^-1};
  (4) the four-jump construction: for every p in P(r) (r <= RMAX) there are h_0..h_3 with
      |h_t| <= 2r+3, h_t(1/2) = p, beta_{h_t}(1/2) = t;
  (5) ping-pong: alpha = x1 and beta = x1 x0^-1 map J = [1/2,3/4) onto [1/2,5/8) and
      [5/8,3/4); hence |P(2L)| >= 2^L; and the exact sizes |P(r)| for r <= RMAX.
usage: python3 lamp_forcing.py  (writes lamp_forcing.json next to this file)
"""
import json
import math
import os
from fractions import Fraction as Q
from itertools import product

RMAX = 12
WORDLEN = 7
HALF = Q(1, 2)


class PL:
    """Increasing PL homeomorphism of [0,1], given by its breakpoint list (x_i, y_i)."""

    def __init__(self, pts):
        pts = sorted(set(pts))
        # drop collinear interior points
        out = [pts[0]]
        for i in range(1, len(pts) - 1):
            (a, b), (c, d), (e, f) = out[-1], pts[i], pts[i + 1]
            if (d - b) * (e - c) != (f - d) * (c - a):
                out.append(pts[i])
        out.append(pts[-1])
        self.pts = tuple(out)

    def __call__(self, t):
        p = self.pts
        for i in range(len(p) - 1):
            (a, b), (c, d) = p[i], p[i + 1]
            if a <= t <= c:
                return b + (d - b) * (t - a) / (c - a)
        raise ValueError(t)

    def inv(self):
        return PL([(y, x) for x, y in self.pts])

    def after(self, other):
        """self o other."""
        xs = {x for x, _ in other.pts} | {other.inv()(x) for x, _ in self.pts}
        return PL([(x, self(other(x))) for x in xs])

    def slope(self, t, side):
        p = self.pts
        for i in range(len(p) - 1):
            (a, b), (c, d) = p[i], p[i + 1]
            if (side > 0 and a <= t < c) or (side < 0 and a < t <= c):
                return (d - b) / (c - a)
        raise ValueError(t)

    def beta(self, t):
        """log2 y'(t+) - log2 y'(t-) at an interior point t (exact: slopes are powers of 2)."""
        r = self.slope(t, +1) / self.slope(t, -1)
        k = round(math.log2(r))
        assert Q(2) ** k == r
        return k

    def breaks(self):
        return [x for x, _ in self.pts[1:-1]]

    def __eq__(self, o):
        return self.pts == o.pts

    def __hash__(self):
        return hash(self.pts)


ID = PL([(Q(0), Q(0)), (Q(1), Q(1))])
X0 = PL([(Q(0), Q(0)), (Q(1, 2), Q(1, 4)), (Q(3, 4), Q(1, 2)), (Q(1), Q(1))])
X1 = PL([(Q(0), Q(0)), (Q(1, 2), Q(1, 2)), (Q(3, 4), Q(5, 8)), (Q(7, 8), Q(3, 4)), (Q(1), Q(1))])
LET = {"a": X0, "A": X0.inv(), "b": X1, "B": X1.inv()}
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def word(w):
    """Word read left to right as a product: 'ab' = x0 * x1 = x0 o x1."""
    g = ID
    for ch in reversed(w):
        g = LET[ch].after(g)
    return g


def reduced_words(n):
    out = [""]
    frontier = [""]
    for _ in range(n):
        nxt = []
        for w in frontier:
            for ch in "aAbB":
                if w and INV[w[-1]] == ch:
                    continue
                nxt.append(w + ch)
        out += nxt
        frontier = nxt
    return out


def check_binary():
    """(1) binary action, on all dyadic words of length <= 6 after the prefix."""
    bad = 0
    for L in range(0, 7):
        for bits in product("01", repeat=L):
            w = "".join(bits)
            val = lambda s: sum(Q(int(c), 2 ** (i + 1)) for i, c in enumerate(s))
            rules = [(X0, "0" + w, "00" + w), (X0, "10" + w, "01" + w), (X0, "11" + w, "1" + w),
                     (X1, "0" + w, "0" + w), (X1, "10" + w, "100" + w),
                     (X1, "110" + w, "101" + w), (X1, "111" + w, "11" + w)]
            for g, s, t in rules:
                if g(val(s)) != val(t):
                    bad += 1
    return bad


def check_letters():
    rec = {}
    for ch, g in LET.items():
        br = g.breaks()
        rec[ch] = {"breaks": [str(x) for x in br], "jumps": [g.beta(x) for x in br]}
        assert len(br) <= 3 and all(abs(j) == 1 for j in rec[ch]["jumps"])
    return rec


def check_break_bound():
    worst = 0.0
    seen = {}
    for w in reduced_words(WORDLEN):
        g = word(w)
        if g in seen and len(seen[g]) <= len(w):
            continue
        seen[g] = w
    # |Br(g)| <= 3 * (shortest word found); and |beta_g(t)| <= |g|
    for g, w in seen.items():
        n = len(w)
        br = g.breaks()
        assert len(br) <= 3 * n, (w, br)
        assert all(abs(g.beta(x)) <= n for x in br)
        if n:
            worst = max(worst, len(br) / n)
    return {"elements": len(seen), "max_breaks_per_letter": worst}


def check_cocycle(ws):
    cnt = 0
    for u in ws:
        for v in ws:
            g, y = word(u), word(v)
            gy = g.after(y)
            pts = set(gy.inv().breaks()) | set(y.inv().breaks()) | set(g.inv().breaks()) | {HALF}
            pts |= {g(t) for t in y.inv().breaks()}
            for t in pts:
                if not (0 < t < 1):
                    continue
                lhs = gy.inv().beta(t)
                rhs = y.inv().beta(g.inv()(t)) + g.inv().beta(t)
                assert lhs == rhs, (u, v, t)
                cnt += 1
    return cnt


def schreier_ball(rmax):
    """P(r) = {h(1/2) : |h| <= r}, with a witness word of minimal length for each point."""
    wit = {HALF: ""}
    frontier = [HALF]
    sizes = [1]
    for _ in range(rmax):
        nxt = []
        for x in frontier:
            for ch in "aAbB":
                y = LET[ch](x)
                if y not in wit:
                    wit[y] = ch + wit[x]     # h = s o h_old, word read left to right
                    nxt.append(y)
        frontier = nxt
        sizes.append(len(wit))
    return wit, sizes


def check_four_jump(wit, rmax):
    worst = 0
    for p, w in wit.items():
        r = len(w)
        h0 = word(w)
        assert h0(HALF) == p
        j = h0.beta(HALF)
        assert abs(j) <= r
        for t in range(4):
            k = t - j
            tail = ("B" if k > 0 else "b") * abs(k)       # x1^{-k}
            ht = word(w + tail)
            assert ht(HALF) == p and ht.beta(HALF) == t
            assert len(w + tail) <= 2 * r + 3
            worst = max(worst, len(w + tail) - 2 * r)
    return worst


def check_pingpong():
    al, be = X1, word("bA")
    J = (Q(1, 2), Q(3, 4))
    ia = (al(J[0]), al(J[1]))
    ib = (be(J[0]), be(J[1]))
    assert ia == (Q(1, 2), Q(5, 8)) and ib == (Q(5, 8), Q(3, 4))
    # affine on J
    assert all(be(t) == t / 2 + Q(3, 8) for t in [Q(1, 2), Q(9, 16), Q(5, 8), Q(11, 16), Q(3, 4)])
    # distinct images of 1/2 under all words of length L in {alpha, beta}, L <= 10
    ok = True
    for L in range(11):
        pts = set()
        for ws in product((al, be), repeat=L):
            x = HALF
            for g in reversed(ws):
                x = g(x)
            pts.add(x)
        ok &= len(pts) == 2 ** L
    return {"alpha": "x1", "beta": "x1 x0^-1", "alpha(J)": [str(v) for v in ia],
            "beta(J)": [str(v) for v in ib], "distinct_2^L_up_to_L10": ok}


def main():
    res = {}
    res["binary_action_mismatches"] = check_binary()
    res["letters"] = check_letters()
    res["break_bound"] = check_break_bound()
    res["cocycle_checks"] = check_cocycle(reduced_words(3))
    wit, sizes = schreier_ball(RMAX)
    res["P_sizes"] = sizes
    res["four_jump_max_len_minus_2r"] = check_four_jump(wit, RMAX)
    res["pingpong"] = check_pingpong()
    res["P_lower_bound_2^floor(r/2)_holds"] = all(sizes[r] >= 2 ** (r // 2) for r in range(RMAX + 1))
    res["R_lower_bound_ceil_P/12_at_m=2r+3"] = {2 * r + 3: -(-sizes[r] // 12) for r in range(RMAX + 1)}
    res["growth_ratios"] = [round(sizes[r + 1] / sizes[r], 4) for r in range(RMAX)]
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lamp_forcing.json")
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
