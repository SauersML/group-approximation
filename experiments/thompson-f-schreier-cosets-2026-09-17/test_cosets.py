#!/usr/bin/env python3
"""Randomised checks of canon():
  (a) canon(f o eta) == canon(f) for eta in H (invariance: same coset -> same key);
  (b) canon(canon(f)) == canon(f);
  (c) canon(f) is f o (element of H) -- by construction; we re-verify that
      canon(f)^-1 o f maps every tile onto a tile with a common shift s and that
      x0^-s o (canon(f)^-1 o f) restricted to each tile is a power of h_k.
Also counts |H cap B_r| by brute force over the Cayley ball (for comparison with
the growth rate 1.48 reported on the live bus).
"""
import random, sys, json
from cosets import *

H0 = canon_pts([(0, 0)] + bump_power_pieces(0, 1) + [(ONE, ONE)])
HGENS = [X0, inv(X0), H0, inv(H0)]


def word(gens, n, rng):
    f = IDENT
    for _ in range(n):
        f = comp(rng.choice(gens), f)
    return f


def in_H(e):
    """independent membership test for H via the tile/bump description."""
    # shift: e(I_0) must be a tile I_s
    a, b = tile(0)
    ea, eb = ev(e, a), ev(e, b)
    s = tile_index(ea)
    if tile(s) != (ea, eb):
        return False
    d = comp(x0pow(-s), e)  # should fix every tile and be a finite product of h_k^n
    pts = [(0, 0)]
    for x in d[0][1:-1]:
        pass
    ks = set()
    for x in d[0][1:-1]:
        k = tile_index(x)
        ks.add(k)
    eta = [(0, 0)]
    for k in sorted(ks, key=lambda k: tile(k)[0]):
        a, b = tile(k)
        if ev(d, a) != a or ev(d, b) != b:
            return False
        n = -slope_right(d, a)  # h_k^n has left slope 2^-n
        eta.extend(bump_power_pieces(k, n))
    eta.append((ONE, ONE))
    ded = []
    for p in eta:
        if ded and ded[-1][0] == p[0]:
            if ded[-1][1] != p[1]:
                return False
            continue
        ded.append(p)
    return canon_pts(ded) == d


def main():
    rng = random.Random(1)
    nt = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    for t in range(nt):
        f = word(GENS, rng.randint(0, 14), rng)
        c = canon(f)
        assert canon(c) == c, "idempotence"
        eta = word(HGENS, rng.randint(1, 12), rng)
        assert in_H(eta)
        assert canon(comp(f, eta)) == c, "invariance"
        assert in_H(comp(inv(c), f)), "canon stays in coset"
    print("random checks ok:", nt)
    # brute-force Cayley ball and H-membership counts
    ball = {IDENT: 0}
    frontier = [IDENT]
    out = {}
    for r in range(1, 9):
        nf = []
        for f in frontier:
            for g in GENS:
                h = comp(g, f)
                if h not in ball:
                    ball[h] = r
                    nf.append(h)
        frontier = nf
        inh = sum(1 for f in ball if in_H(f))
        cos = len({canon(inv(f)) for f in ball})
        out[r] = dict(cayley=len(ball), H_cap_ball=inh, cosets_hit=cos)
        print(r, out[r], flush=True)
    json.dump(out, open("test_cosets.json", "w"), indent=1)


if __name__ == "__main__":
    main()
