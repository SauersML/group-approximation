# Exact (rational, no sampling) version of gaps.py.
# For every direction w in R^2 \ 0 and every k in 1..5, exhibit a cyclically reduced word x of length <= 5
# with ev[k-1](x, w) == ev[k](x, w), where ev are the sorted eigenvalue valuations of LK_4(x) under the
# monomial valuation w = (v(q), v(t)).
# Method: the eigenvalue valuations are piecewise linear in w. Their combinatorics (which monomial attains
# each coefficient minimum, and which Newton points lie on the lower hull) can only change on "critical"
# rays: w orthogonal to m - m' (two monomials of one coefficient) or to a collinearity vector of three Newton
# points. Between consecutive critical rays everything is linear and the tie pattern is constant. So it is
# enough to test every critical ray and one interior ray of every arc. All arithmetic is exact.
import pickle, sys, math
from fractions import Fraction
from math import gcd

res = pickle.load(open(sys.argv[1], 'rb'))
words = sorted(res, key=lambda x: (len(x), x))

def norm(v):
    a, b = v
    g = gcd(abs(a), abs(b))
    return (a // g, b // g) if g else None

crit = set()
def add_normal(d):
    d = norm(d)
    if d is None:
        return
    crit.add((-d[1], d[0])); crit.add((d[1], -d[0]))

# (a) monomial ties
for x in words:
    for k, mons in res[x].items():
        for i in range(len(mons)):
            for j in range(i + 1, len(mons)):
                add_normal((mons[i][0] - mons[j][0], mons[i][1] - mons[j][1]))
print('type (a) critical rays:', len(crit))

def ang(w):
    return math.atan2(w[1], w[0])

def arcs(dirs):
    ds = sorted(dirs, key=ang)
    out = []
    for i in range(len(ds)):
        u, v = ds[i], ds[(i + 1) % len(ds)]
        m = (u[0] + v[0], u[1] + v[1])  # interior ray (arcs are < 180 degrees)
        if m != (0, 0):
            out.append(m)
    return ds, out

def attaining(cp, w):
    pts = []
    for k in sorted(cp):
        if not cp[k]:
            continue
        best = min(cp[k], key=lambda m: m[0] * w[0] + m[1] * w[1])
        pts.append((k, best))
    return pts

# (b) collinearity rays, per arc of the type (a) fan
_, mids = arcs(crit)
coll = set()
for w in mids:
    for x in words:
        pts = attaining(res[x], w)
        n = len(pts)
        for i in range(n):
            for j in range(i + 1, n):
                for l in range(j + 1, n):
                    (k1, m1), (k2, m2), (k3, m3) = pts[i], pts[j], pts[l]
                    d = ((m2[0] - m1[0]) * (k3 - k1) - (m3[0] - m1[0]) * (k2 - k1),
                         (m2[1] - m1[1]) * (k3 - k1) - (m3[1] - m1[1]) * (k2 - k1))
                    dn = norm(d)
                    if dn:
                        coll.add((-dn[1], dn[0])); coll.add((dn[1], -dn[0]))
crit |= coll
ds, mids = arcs(crit)
tests = ds + mids
print('critical rays total:', len(ds), ' test rays:', len(tests))

def eig_vals(cp, w):
    pts = [(k, min(w[0] * i + w[1] * j for (i, j) in cp[k])) for k in sorted(cp) if cp[k]]
    hull = []
    for p in pts:
        while len(hull) >= 2 and (hull[-1][1] - hull[-2][1]) * (p[0] - hull[-2][0]) >= (p[1] - hull[-2][1]) * (hull[-1][0] - hull[-2][0]):
            hull.pop()
        hull.append(p)
    vals = []
    for (k0, v0), (k1, v1) in zip(hull, hull[1:]):
        vals += [Fraction(-(v1 - v0), k1 - k0)] * (k1 - k0)
    return sorted(vals)

uniform = {k: [] for k in range(1, 6)}
witness_len = {k: 0 for k in range(1, 6)}
for w in tests:
    need = set(range(1, 6))
    for x in words:
        ev = eig_vals(res[x], w)
        for k in list(need):
            if ev[k - 1] == ev[k]:
                need.discard(k)
                witness_len[k] = max(witness_len[k], len(x))
        if not need:
            break
    for k in need:
        uniform[k].append(w)
for k in range(1, 6):
    print('gap', k, ': test rays with a uniform gap:', len(uniform[k]), uniform[k][:5],
          '; longest witness needed:', witness_len[k])
