"""Brute-force search for collisions of growth rules on finite configurations.

Group: G = Z/2 * Z/2 * Z/2 = <s,t,u | s^2, t^2, u^2>, whose right Cayley graph
is the 3-regular tree.  A configuration over {c,1} that is finite w.r.t. the
background c is a finite set S of sites.  A growth rule keeps every site of S
(so c is never created) and turns a c-site g into 1 according to a local test
on (x(gs), x(gt), x(gu)).  The rule is injective on Fin_c iff S -> T(S) is
injective on finite subsets.

This script enumerates every subset S of the ball of radius R around 1 and
reports collisions T(S) = T(S') inside that family.  Absence of collisions is
only a necessary condition; the proof is in the research node.

Usage: python3 ball_collisions.py RULE R
RULE: 'leaf'   created iff exactly one neighbour is in S
      'two'    created iff exactly two neighbours are in S
"""
import sys
import numpy as np

GENS = "stu"


def ball(radius):
    words = [""]
    frontier = [""]
    for _ in range(radius):
        nxt = []
        for w in frontier:
            for x in GENS:
                if not w or w[-1] != x:
                    nxt.append(w + x)
        words += nxt
        frontier = nxt
    return words


def mul(w, x):
    return w[:-1] if w and w[-1] == x else w + x


def run(rule, R):
    dom = ball(R)
    img = ball(R + 1)
    didx = {w: i for i, w in enumerate(dom)}
    n = len(dom)
    S = np.arange(1 << n, dtype=np.uint64)
    T = np.zeros(1 << n, dtype=np.uint64)
    one = np.uint64(1)
    for j, w in enumerate(img):
        inS = ((S >> np.uint64(didx[w])) & one) if w in didx else np.zeros_like(S)
        cnt = np.zeros_like(S)
        for x in GENS:
            v = mul(w, x)
            if v in didx:
                cnt += (S >> np.uint64(didx[v])) & one
        if rule == "leaf":
            created = (cnt == 1)
        elif rule == "two":
            created = (cnt == 2)
        else:
            raise SystemExit("unknown rule")
        bit = inS.astype(bool) | (created & (inS == 0))
        T |= bit.astype(np.uint64) << np.uint64(j)
    order = np.argsort(T, kind="stable")
    Ts = T[order]
    dup = np.nonzero(Ts[1:] == Ts[:-1])[0]
    print(f"rule={rule} R={R} |ball|={n} subsets={1 << n} collisions={len(dup)}")
    for k in dup[:5]:
        a, b = int(order[k]), int(order[k + 1])
        sa = [dom[i] or "1" for i in range(n) if a >> i & 1]
        sb = [dom[i] or "1" for i in range(n) if b >> i & 1]
        tt = [img[i] or "1" for i in range(len(img)) if int(Ts[k]) >> i & 1]
        print("  S =", sa, " S' =", sb, " T =", tt)


if __name__ == "__main__":
    run(sys.argv[1], int(sys.argv[2]))
