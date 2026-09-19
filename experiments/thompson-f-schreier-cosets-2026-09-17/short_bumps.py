#!/usr/bin/env python3
"""Scouting: shortest elements w of F whose support is exactly one closed fundamental
domain [c, x0^-1(c)] of x0 and which are one-bump there (w(t) != t on the open
domain).  For such w, <x0, w> = Z wr Z and the decorated-tiling argument applies
(with b_I replaced by w and its x0-conjugates, provided w has no root)."""
from cosets import *
import json

X0I = inv(X0)


def support(f):
    """(lo, hi) closure of the support, and whether f moves every point of (lo,hi)."""
    xs, ys = f
    moved = [i for i in range(len(xs) - 1) if not (xs[i] == ys[i] and xs[i + 1] == ys[i + 1])]
    if not moved:
        return None
    lo = xs[moved[0]]
    hi = xs[moved[-1] + 1]
    # fixed points strictly inside (lo, hi): breakpoints with x == y, or linear pieces crossing diagonal
    onebump = True
    for i in range(len(xs) - 1):
        a, b = xs[i], xs[i + 1]
        if b <= lo or a >= hi:
            continue
        if lo < a < hi and xs[i] == ys[i]:
            onebump = False
        if xs[i] == ys[i] and xs[i + 1] == ys[i + 1] and lo <= a and b <= hi:
            onebump = False
        # crossing inside the piece
        d0, d1 = ys[i] - xs[i], ys[i + 1] - xs[i + 1]
        if d0 * d1 < 0:
            onebump = False
    return lo, hi, onebump


def main():
    ball = {IDENT: ()}
    frontier = [(IDENT, ())]
    names = ["a", "A", "b", "B"]
    found = []
    for r in range(1, 10):
        nf = []
        for f, w in frontier:
            for gi, g in enumerate(GENS):
                h = comp(g, f)
                if h not in ball:
                    ball[h] = w + (gi,)
                    nf.append((h, w + (gi,)))
                    s = support(h)
                    if s and s[2] and ev(X0I, s[0]) == s[1]:
                        found.append(("".join(names[i] for i in w + (gi,)), r, s[0] / ONE, s[1] / ONE))
        frontier = nf
        print(r, len(ball), "domain-bumps so far", len(found), flush=True)
        if len(found) >= 40:
            break
    for x in found[:40]:
        print(x)
    json.dump(found, open("short_bumps.json", "w"), indent=1)


if __name__ == "__main__":
    main()
