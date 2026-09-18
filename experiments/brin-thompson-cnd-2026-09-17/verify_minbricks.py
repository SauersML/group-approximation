"""Independent check of lib2v.min_bricks.

Brute force: minimal brick count = min over ALL guillotine partitions (every dyadic brick
partition has a midline cut), both split directions always allowed, depth capped at the
maximal domain word length of the input diagram + 1 per axis. Canonicity of g on [u]x[v]
is tested directly: restrict all diagram bricks to [u]x[v] and check that all restricted
bricks (u s, v t) -> (R_x, R_y) have a common U, V with R_x = U s, R_y = V t.

Usage: python3 verify_minbricks.py [--trials N]
"""
import argparse
import random
from functools import lru_cache

import lib2v as V


def canonical_direct(g, u, v):
    U = W = None
    for (dx, dy, rx, ry) in g:
        if not (V._cmp(dx, u) and V._cmp(dy, v)):
            continue
        ix = dx if len(dx) >= len(u) else u
        iy = dy if len(dy) >= len(v) else v
        Rx = rx + ix[len(dx):]
        Ry = ry + iy[len(dy):]
        sx, sy = ix[len(u):], iy[len(v):]
        if len(Rx) < len(sx) or len(Ry) < len(sy):
            return False
        if Rx[len(Rx) - len(sx):] != sx or Ry[len(Ry) - len(sy):] != sy:
            return False
        u0, w0 = Rx[:len(Rx) - len(sx)], Ry[:len(Ry) - len(sy)]
        if U is None:
            U, W = u0, w0
        elif (U, W) != (u0, w0):
            return False
    return True


def brute(g):
    D = max(max(len(b[0]), len(b[1])) for b in g) + 1

    @lru_cache(maxsize=None)
    def cost(u, v):
        if canonical_direct(g, u, v):
            return 1
        best = 10 ** 9
        if len(u) < D:
            best = min(best, cost(u + "0", v) + cost(u + "1", v))
        if len(v) < D:
            best = min(best, cost(u, v + "0") + cost(u, v + "1"))
        return best

    return cost("", "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=300)
    args = ap.parse_args()
    rng = random.Random(7)
    words = [["x1x"], ["bak'", "c0y'", "c1y", "c0y"], ["x0x", "c0y"], ["c0y'", "x1x"], ["x0x"]]
    elts = [V.word_element(w) for w in words]
    gi = [V.inverse(g) for g in elts]
    pairs = [V.reduce_greedy(V.compose(gi[i], elts[j])) for i in range(5) for j in range(5)]
    for t in range(args.trials):
        pairs.append(V.word_element(V.random_word(rng.randint(0, 5), rng)))
    bad = 0
    for g in pairs:
        a, b = V.min_bricks(g), brute(g)
        if a != b:
            bad += 1
            print("MISMATCH", a, b, g)
    print(f"checked {len(pairs)} elements, mismatches {bad}")


if __name__ == "__main__":
    main()
