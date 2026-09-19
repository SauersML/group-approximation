"""Exact breakpoints of s on each fundamental window W_n = delta^n [X, delta X):
count, and the largest gap between consecutive breakpoints (the scale-periodic
kill needs gaps -> infinity; for delta = 2x they grow like 2^n)."""
import sys
from fast import *


def gaps(ch, name, N):
    print(f"== {name}")
    lo = ch.X
    for n in range(N):
        hi = ch.delta(lo)[0]
        x, bps = lo, []
        prev = None
        while x < hi:
            y, a, r = ch.s(x)
            if prev is not None and a != prev:
                bps.append(x)
            prev = a
            x = x + r
        g = [b - a for a, b in zip(bps, bps[1:])]
        mg = f(max(g)) if g else None
        print(f"n={n:2d} W=[{f(lo):.6g},{f(hi):.6g}) len {f(hi-lo):.5g}: "
              f"{len(bps)} slope-breaks, max gap {mg}, max gap/len "
              f"{(mg / f(hi - lo)) if mg else None}")
        sys.stdout.flush()
        lo = hi


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    gaps(affine_control(), "affine control", N)
    gaps(nonaffine(), "non-affine", N)
