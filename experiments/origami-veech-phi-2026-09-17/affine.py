"""Exact affine maps of a scaled origami, acting on grid vertices.

O is an origami (B, C permutations of n unit squares). O_m subdivides each square into m x m.
X_m = small squares (i, u, v), identified with their lower-left grid vertex. An affine map f of O
with derivative A in SL_2(Z) that fixes the set of corners of O acts exactly on the non-corner
vertices; we compute it by developing straight segments with a generic infinitesimal offset.
Corner vertices are patched by the identity (a bounded-rank patch)."""
from fractions import Fraction as Fr
from perm import inv

DELTA = (Fr(1), Fr(1, 1000003))  # generic infinitesimal direction


class Corner(Exception):
    pass


def lt(p, q):
    return p < q  # tuples (main, eps) compare lexicographically


def develop(B, C, Bi, Ci, pt, w):
    """pt = (j, (xa, xb), (ya, yb)) meaning x = xa + eps xb in [0,1). Move by main vector w."""
    j, (xa, xb), (ya, yb) = pt
    ra, rb = Fr(1), Fr(0)
    wx, wy = w
    while True:
        cand = []
        if wx > 0:
            cand.append((((1 - xa) / wx, -xb / wx), "R"))
        elif wx < 0:
            cand.append((((-xa) / wx, -xb / wx), "L"))
        if wy > 0:
            cand.append((((1 - ya) / wy, -yb / wy), "U"))
        elif wy < 0:
            cand.append((((-ya) / wy, -yb / wy), "D"))
        cand = [c for c in cand if c[0] <= (ra, rb)]
        if not cand:
            return (j, (xa + ra * wx, xb + rb * wx), (ya + ra * wy, yb + rb * wy))
        cand.sort()
        if len(cand) > 1 and cand[0][0] == cand[1][0]:
            raise Corner()
        (ta, tb), dirn = cand[0]
        # move to the crossing (main part only; offsets move with the eps part of t)
        xa, xb = xa + ta * wx, xb + tb * wx
        ya, yb = ya + ta * wy, yb + tb * wy
        ra, rb = ra - ta, rb - tb
        if dirn == "R":
            j, xa = B[j], xa - 1
        elif dirn == "L":
            j, xa = Bi[j], xa + 1
        elif dirn == "U":
            j, ya = C[j], ya - 1
        else:
            j, ya = Ci[j], ya + 1


def affine_map(B, C, m, A, jstart, corner):
    """Affine map with derivative A sending the lower-left sector of square 0's corner to the
    corner `corner` in {0,1}^2 of square jstart. Returns permutation of X_m, or None if invalid."""
    n = len(B)
    Bi, Ci = inv(B), inv(C)
    Ad = (A[0][0] * DELTA[0] + A[0][1] * DELTA[1], A[1][0] * DELTA[0] + A[1][1] * DELTA[1])
    cx, cy = corner
    if (cx == 1) != (Ad[0] < 0) or (cy == 1) != (Ad[1] < 0):
        return None
    start = (jstart, (Fr(cx), Ad[0]), (Fr(cy), Ad[1]))
    Av = lambda x, y: (A[0][0] * x + A[0][1] * y, A[1][0] * x + A[1][1] * y)
    try:
        img = {0: develop(B, C, Bi, Ci, start, Av(Fr(1, 2), Fr(1, 2)))}
        stack = [0]
        while stack:
            i = stack.pop()
            for nb, vec in ((B[i], (1, 0)), (Bi[i], (-1, 0)), (C[i], (0, 1)), (Ci[i], (0, -1))):
                p = develop(B, C, Bi, Ci, img[i], Av(*vec))
                if nb in img:
                    if (img[nb][0], img[nb][1][0], img[nb][2][0]) != (p[0], p[1][0], p[2][0]):
                        return None
                else:
                    img[nb] = p
                    stack.append(nb)
        f = [-1] * (n * m * m)
        for i in range(n):
            for u in range(m):
                for v in range(m):
                    idx = (i * m + u) * m + v
                    if u == 0 and v == 0:
                        continue
                    j, (xa, xb), (ya, yb) = develop(B, C, Bi, Ci, img[i], Av(Fr(u, m) - Fr(1, 2), Fr(v, m) - Fr(1, 2)))
                    if xa == 1:
                        j, xa = B[j], Fr(0)
                    if ya == 1:
                        j, ya = C[j], Fr(0)
                    if xa * m != int(xa * m) or ya * m != int(ya * m) or (xa == 0 and ya == 0):
                        return None
                    f[idx] = (j * m + int(xa * m)) * m + int(ya * m)
    except Corner:
        return None
    for i in range(n):
        f[(i * m) * m] = (i * m) * m
    if sorted(f) != list(range(n * m * m)):
        return None
    return tuple(f)


S_MAT = ((0, -1), (1, 0))
T_MAT = ((1, 1), (0, 1))


def lifts(B, C, m, A):
    out = []
    for j in range(len(B)):
        for corner in ((0, 0), (1, 0), (0, 1), (1, 1)):
            f = affine_map(B, C, m, A, j, corner)
            if f is not None and f not in out:
                out.append(f)
    return out
