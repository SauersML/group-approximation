"""Collision search for further binary growth rules on the 3-regular tree.

Same setting as ball_collisions.py.  Rules here may look at the radius-2 ball.

  leaf2 : g is created iff g is not in S and S meets the closed 2-ball of g
          in exactly one point, which is a neighbour of g.

Usage: python3 rules_search.py RULE R
"""
import sys
import numpy as np
from ball_collisions import ball, mul, GENS


def sphere_words(w):
    """Neighbours and distance-two points of w, as two lists."""
    nb = [mul(w, x) for x in GENS]
    d2 = [mul(v, y) for v in nb for y in GENS if mul(v, y) != w]
    return nb, d2


def run(rule, R):
    dom = ball(R)
    img = ball(R + 1)
    didx = {w: i for i, w in enumerate(dom)}
    n = len(dom)
    S = np.arange(1 << n, dtype=np.uint64)
    one = np.uint64(1)
    zero = np.zeros_like(S)

    def bit(w):
        return ((S >> np.uint64(didx[w])) & one) if w in didx else zero

    T = np.zeros_like(S)
    for j, w in enumerate(img):
        inS = bit(w).astype(bool)
        nb, d2 = sphere_words(w)
        cnt1 = sum(bit(v) for v in nb)
        cnt2 = sum(bit(v) for v in d2)
        if rule == "leaf2":
            created = (cnt1 == 1) & (cnt2 == 0)
        else:
            raise SystemExit("unknown rule")
        T |= (inS | created).astype(np.uint64) << np.uint64(j)
    order = np.argsort(T, kind="stable")
    Ts = T[order]
    dup = np.nonzero(Ts[1:] == Ts[:-1])[0]
    print(f"rule={rule} R={R} |ball|={n} subsets={1 << n} collisions={len(dup)}")
    for k in dup[:5]:
        a, b = int(order[k]), int(order[k + 1])
        sa = [dom[i] or "1" for i in range(n) if a >> i & 1]
        sb = [dom[i] or "1" for i in range(n) if b >> i & 1]
        print("  S =", sa, " S' =", sb)


if __name__ == "__main__":
    run(sys.argv[1], int(sys.argv[2]))
