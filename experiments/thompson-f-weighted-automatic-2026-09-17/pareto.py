#!/usr/bin/env python3
"""Pareto (x0-count, x1-count) profiles of words over A={x0^±1,x1^±1} in Thompson's group F.
For every element g reachable by a word with at most R letters, compute the set of
nondominated pairs (n0, n1) over all words for g with n0+n1 <= R.  If every g with
|g| <= R - slack has a single nondominated pair (m0, m1) with m0+m1=|g|, then every
positive weighting (p,q) has the same geodesic words as the standard metric (within range).
Usage: pareto.py R"""
import sys
from fractions import Fraction as Q
sys.path.insert(0, __file__.rsplit('/', 1)[0])

def norm(nodes):
    out = [nodes[0]]
    for i in range(1, len(nodes) - 1):
        (xa, ya), (xb, yb), (xc, yc) = out[-1], nodes[i], nodes[i + 1]
        if (yb - ya) * (xc - xb) != (yc - yb) * (xb - xa):
            out.append(nodes[i])
    out.append(nodes[-1])
    return tuple(out)

def ev(f, t):
    lo, hi = 0, len(f) - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if f[mid][0] <= t:
            lo = mid
        else:
            hi = mid
    (xa, ya), (xb, yb) = f[lo], f[hi]
    return ya + (yb - ya) * (t - xa) / (xb - xa)

def inv(f):
    return tuple((y, x) for (x, y) in f)

def rmul(f, s):
    """f then s: t -> s(f(t))."""
    pts = set(x for x, _ in f)
    fi = inv(f)
    for (x, _) in s:
        pts.add(ev(fi, x))
    xs = sorted(pts)
    return norm(tuple((x, ev(s, ev(f, x))) for x in xs))

ID = ((Q(0), Q(0)), (Q(1), Q(1)))
X0 = norm(((Q(0), Q(0)), (Q(1, 2), Q(1, 4)), (Q(3, 4), Q(1, 2)), (Q(1), Q(1))))
X1 = norm(((Q(0), Q(0)), (Q(1, 2), Q(1, 2)), (Q(3, 4), Q(5, 8)), (Q(7, 8), Q(3, 4)), (Q(1), Q(1))))
GENS = [(X0, (1, 0)), (inv(X0), (1, 0)), (X1, (0, 1)), (inv(X1), (0, 1))]

def main(R):
    labels = {ID: {(0, 0)}}
    frontier = {ID: {(0, 0)}}
    dist = {ID: 0}
    for L in range(1, R + 1):
        new = {}
        for g, labs in frontier.items():
            for s, (d0, d1) in GENS:
                h = rmul(g, s)
                for (a, b) in labs:
                    lab = (a + d0, b + d1)
                    old = labels.get(h)
                    if old is not None and any(o0 <= lab[0] and o1 <= lab[1] for (o0, o1) in old):
                        continue
                    new.setdefault(h, set()).add(lab)
        for h, labs in new.items():
            old = labels.setdefault(h, set())
            # labs all have total L; none dominated by old (checked), old may not be dominated by them (old total < L)
            labs = {l for l in labs if not any(o[0] <= l[0] and o[1] <= l[1] and o != l for o in old | labs)}
            old |= labs
            new[h] = labs
            dist.setdefault(h, L)
        frontier = new
        multi = [(g, sorted(labels[g])) for g in labels if len(labels[g]) > 1]
        excess = [(g, sorted(labels[g])) for g in labels if max(a + b for a, b in labels[g]) > dist[g]]
        print("L=%d elements=%d multi-Pareto=%d with-excess-label=%d" % (L, len(labels), len(multi), len(excess)), flush=True)
        for g, labs in (excess[:6] if L == R else []):
            print("   |g|=%d labels=%s breakpoints=%s" % (dist[g], labs, [(str(x), str(y)) for x, y in g]), flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]))
