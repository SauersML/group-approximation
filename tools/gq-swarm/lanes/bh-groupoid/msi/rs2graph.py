"""Robertson-Steger 2-graph of Gamma_T for a triangle presentation T over PG(2,2).

Apartment coordinates: vertex i*w1 + j*w2, type i + 2j mod 3.  Type-increasing edges
from p go to p+w1, p-w2, p-w1+w2; each carries a label in P.

Tile (shape (1,1) word) at the origin, labels (x,y,z,u,w):
  up triangle   0 -> w1 -> w2 -> 0            labels (x, y, z),  (x,y,z) in T
  down triangle w2 -> w1+w2 -> w1 -> w2       labels (u, w, y),  (u,w,y) in T
nondegenerate iff the two triangles on the diagonal edge differ, i.e. u != z.
Gamma_T acts simply transitively on vertices, so Gamma-orbits of tiles are label tuples.

Edges of colour 1: a -> b when tile b sits at w1 next to a: w_a = z_b, y_a != x_b.
Edges of colour 2: a -> c when tile c sits at w2 above a:  u_a = x_c, w_a != y_c.
(The inequalities are the nonfolding conditions on the shared edge.)
A shape (2,2) word t00, t10, t01, t11 gives the square
   (t00 -1-> t10)(t10 -2-> t11) = (t00 -2-> t01)(t01 -1-> t11).
"""
import itertools
from collections import defaultdict

P = range(7)  # overridden by build(T, npoints)


def build(T, npoints=7):
    P = range(npoints)
    T = set(map(tuple, T))
    nxt = {(x, y): z for (x, y, z) in T}
    tiles = []
    for (x, y, z) in sorted(T):
        for u in P:
            if (u, y) in [(a, b) for (b, a) in []]:
                pass
            # down triangle (u, w, y) in T  <=>  (y, u, w) in T
            if (y, u) in nxt and u != z:
                tiles.append((x, y, z, u, nxt[(y, u)]))
    idx = {t: i for i, t in enumerate(tiles)}
    E1 = []  # (a, b)
    E2 = []
    for a in tiles:
        for b in tiles:
            if a[4] == b[2] and a[1] != b[0]:
                E1.append((idx[a], idx[b]))
            if a[3] == b[0] and a[4] != b[1]:
                E2.append((idx[a], idx[b]))
    e1 = {e: i for i, e in enumerate(E1)}
    e2 = {e: i for i, e in enumerate(E2)}
    out1 = defaultdict(list)
    out2 = defaultdict(list)
    for (a, b) in E1:
        out1[a].append(b)
    for (a, b) in E2:
        out2[a].append(b)
    set2 = set(E2)
    set1 = set(E1)
    squares = []  # (e1 index of t00->t10, e2 index t10->t11, e2 index t00->t01, e1 index t01->t11)
    for t00 in range(len(tiles)):
        for t10 in out1[t00]:
            for t11 in out2[t10]:
                cands = [t01 for t01 in out2[t00] if (t01, t11) in set1]
                assert len(cands) == 1, ("H1 fails", t00, t10, t11, cands)
                t01 = cands[0]
                squares.append((e1[(t00, t10)], e2[(t10, t11)], e2[(t00, t01)], e1[(t01, t11)]))
    # the square map must be a bijection from 1-2 paths to 2-1 paths
    assert len({(s[2], s[3]) for s in squares}) == len(squares)
    return tiles, E1, E2, squares


if __name__ == "__main__":
    import json
    ex = json.load(open("tp_q2.json"))["examples"]
    for lam, T, _ in ex:
        tiles, E1, E2, sq = build(T)
        rows1 = {sum(1 for e in E1 if e[0] == a) for a in range(len(tiles))}
        rows2 = {sum(1 for e in E2 if e[0] == a) for a in range(len(tiles))}
        print(len(tiles), "tiles;", len(E1), len(E2), "edges; row sums", rows1, rows2, ";", len(sq), "squares; H1 ok")
