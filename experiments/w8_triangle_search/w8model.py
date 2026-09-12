#!/usr/bin/env python3
"""The symplectic quadrangle W(q), q in {2, 8}, in the coordinates of
`GroupApproximation/GGT/KazhdanHypSymplecticQuadrangle.lean` (which is the case
q = 8), and an element of Sp(4,q) of a prescribed order acting freely on points
and lines (order 65 = q^2+1 for the W(8) search; order 1 or 5 for the W(2)
calibration against the published GQ(2,2) tables).

Coordinates (the Lean module fixes the form, not the field presentation):
  * GF(8) = GF(2)[t]/(t^3 + t + 1), an element is the bit pattern of its
    coefficients (0..7);
  * Vec = GF(8)^4 and B(x,y) = x0*y2 + x1*y3 - x2*y0 - x3*y1, which in
    characteristic two is x0*y2 + x1*y3 + x2*y0 + x3*y1;
  * a point is a nonzero vector whose first nonzero coordinate is 1, the 585
    points listed in lexicographic order of their coordinate tuples;
  * a line is a totally isotropic 2-subspace, recorded as the sorted tuple of
    its 9 point indices, the 585 lines listed in lexicographic order.

The element is a product of random symplectic transvections
x -> x + a*B(x,v)*v, accepted when its order is exactly the prescribed one and
it acts freely on points and on lines.  All cyclic subgroups of order 65 of
Sp(4,8) are conjugate, so the invariant W(8) search does not depend on the seed.

Usage: w8model.py <q> <order> <seed> <out.json>
"""
import itertools
import json
import random
import sys

Q = int(sys.argv[1]) if __name__ == "__main__" else 8
assert Q in (2, 8)
MOD = 0b1011  # t^3 + t + 1 (q = 8)


def gmul(a, b):
    if Q == 2:
        return a & b
    r = 0
    for i in range(3):
        if (b >> i) & 1:
            r ^= a << i
    if (r >> 4) & 1:
        r ^= MOD << 1
    if (r >> 3) & 1:
        r ^= MOD
    return r


INV = [0] * Q
for a in range(1, Q):
    for b in range(1, Q):
        if gmul(a, b) == 1:
            INV[a] = b
assert all(gmul(a, INV[a]) == 1 for a in range(1, Q))
NPTS = (Q ** 4 - 1) // (Q - 1)


def vadd(x, y):
    return tuple(a ^ b for a, b in zip(x, y))


def vscale(c, x):
    return tuple(gmul(c, a) for a in x)


def form(x, y):
    return gmul(x[0], y[2]) ^ gmul(x[1], y[3]) ^ gmul(x[2], y[0]) ^ gmul(x[3], y[1])


def normalize(x):
    for a in x:
        if a:
            return vscale(INV[a], x)
    return None


def build_geometry():
    points = [x for x in itertools.product(range(Q), repeat=4)
              if any(x) and normalize(x) == x]
    assert len(points) == NPTS
    pidx = {x: i for i, x in enumerate(points)}
    lines = set()
    for i, p in enumerate(points):
        for j in range(i + 1, len(points)):
            q = points[j]
            if form(p, q) != 0:
                continue
            span = set()
            for a in range(Q):
                for b in range(Q):
                    if a or b:
                        span.add(pidx[normalize(vadd(vscale(a, p), vscale(b, q)))])
            lines.add(tuple(sorted(span)))
    lines = sorted(lines)
    assert len(lines) == NPTS, len(lines)
    assert all(len(m) == Q + 1 for m in lines)
    point_lines = [[] for _ in points]
    for k, m in enumerate(lines):
        for p in m:
            point_lines[p].append(k)
    assert all(len(ls) == Q + 1 for ls in point_lines)
    return points, pidx, lines, point_lines


IDENT = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))


def mvec(M, x):
    out = []
    for r in range(4):
        s = 0
        for c in range(4):
            s ^= gmul(M[r][c], x[c])
        out.append(s)
    return tuple(out)


def mmul(M, N):
    return tuple(tuple(
        (gmul(M[r][0], N[0][c]) ^ gmul(M[r][1], N[1][c]) ^
         gmul(M[r][2], N[2][c]) ^ gmul(M[r][3], N[3][c]))
        for c in range(4)) for r in range(4))


def mpow(M, n):
    R = IDENT
    B = M
    while n:
        if n & 1:
            R = mmul(R, B)
        B = mmul(B, B)
        n >>= 1
    return R


def transvection(v, a):
    w = (v[2], v[3], v[0], v[1])
    return tuple(tuple(((1 if r == c else 0) ^ gmul(a, gmul(v[r], w[c])))
                       for c in range(4)) for r in range(4))


def symplectic(M):
    cols = [tuple(M[r][c] for r in range(4)) for c in range(4)]
    for a in range(4):
        for b in range(4):
            e = 1 if (a, b) in ((0, 2), (2, 0), (1, 3), (3, 1)) else 0
            if form(cols[a], cols[b]) != e:
                return False
    return True


def orbits(perm):
    seen = [False] * len(perm)
    sizes = []
    for s in range(len(perm)):
        if seen[s]:
            continue
        n = 0
        x = s
        while not seen[x]:
            seen[x] = True
            x = perm[x]
            n += 1
        sizes.append(n)
    return sizes


def prime_divisors(n):
    ps, p = [], 2
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        ps.append(n)
    return ps


def main():
    order = int(sys.argv[2])
    seed = int(sys.argv[3])
    out = sys.argv[4]
    rng = random.Random(seed)
    points, pidx, lines, point_lines = build_geometry()
    lidx = {m: k for k, m in enumerate(lines)}
    assert NPTS % order == 0
    tries = 0
    while True:
        tries += 1
        if tries > 20000:
            sys.exit(f"no element of order {order} acting freely on points and "
                     f"lines of W({Q}) found in 20000 random tries")
        M = IDENT
        if order > 1:
            for _ in range(24):
                v = tuple(rng.randrange(Q) for _ in range(4))
                if not any(v):
                    continue
                M = mmul(M, transvection(v, rng.randrange(1, Q)))
            if mpow(M, order) != IDENT or any(mpow(M, order // p) == IDENT
                                              for p in prime_divisors(order)):
                continue
        assert symplectic(M)
        sp = [pidx[normalize(mvec(M, p))] for p in points]
        sl = [lidx[tuple(sorted(sp[p] for p in m))] for m in lines]
        want = [order] * (NPTS // order)
        if sorted(orbits(sp)) == want and sorted(orbits(sl)) == want:
            break
    with open(out, "w") as fh:
        json.dump({"q": Q, "order": order, "seed": seed, "tries": tries,
                   "matrix": M, "points": points, "lines": lines,
                   "point_lines": point_lines, "sigma_points": sp,
                   "sigma_lines": sl}, fh)
    print(f"model ok: W({Q}), {NPTS} points, {NPTS} lines, free element of order "
          f"{order} after {tries} tries")


if __name__ == "__main__":
    main()
