#!/usr/bin/env python3
"""Test whether every character of B_n Gamma is hyperplane-affine on UD_n Gamma.

Builds Abrams' discretized configuration space X = UD_n Gamma (vertices,
edges, squares) for a subdivided graph, computes over F_p (p large prime):

  b1      = |E| - |V| + 1 - rank(d2)            (first Betti number of X)
  H       = number of hyperplane classes of X
  kerD    = dim { f : V(X) -> F_p : delta f constant on hyperplane classes }
  image   = H - (kerD - 1)                       (rank of F_p^H -> H^1(X))

Every character is hyperplane-affine iff image == b1 (over Q).  With EXACT=1
the ranks are computed over Q with fractions; otherwise over F_p, where
b1_p >= b1_Q and image_p <= image_Q, so F_p runs are evidence only.
Single-threaded, small inputs only.
"""
import itertools, os, sys

P = 1000003


def subdivide(edges, k):
    """Subdivide every edge of a multigraph into k segments.

    k is an int (uniform) or a list with one length per edge."""
    lengths = list(k) if isinstance(k, (list, tuple)) else [k] * len(edges)
    assert len(lengths) == len(edges) and min(lengths) >= 1
    new_edges = []
    for idx, (a, b) in enumerate(edges):
        prev = a
        for j in range(1, lengths[idx]):
            v = ('s', idx, j)
            new_edges.append((prev, v))
            prev = v
        new_edges.append((prev, b))
    vs = set()
    for (a, b) in new_edges:
        vs.add(a); vs.add(b)
    order = {v: i for i, v in enumerate(sorted(vs, key=repr))}
    return len(order), [(order[a], order[b]) for (a, b) in new_edges]


def rank_mod_p(rows, ncols):
    """Rank of a sparse matrix over F_P; rows are dicts col->val."""
    pivots = {}  # col -> row dict (normalized, pivot value 1)
    rank = 0
    for r in rows:
        row = {c: v % P for c, v in r.items() if v % P}
        while row:
            c = min(row)
            if c in pivots:
                f = row[c]
                prow = pivots[c]
                for cc, vv in prow.items():
                    nv = (row.get(cc, 0) - f * vv) % P
                    if nv:
                        row[cc] = nv
                    else:
                        row.pop(cc, None)
            else:
                inv = pow(row[c], P - 2, P)
                row = {cc: (vv * inv) % P for cc, vv in row.items()}
                pivots[c] = row
                rank += 1
                break
    return rank


def rank_exact(rows, ncols):
    """Rank over Q (exact, fractions); for small instances."""
    from fractions import Fraction
    pivots = {}
    rank = 0
    for r in rows:
        row = {c: Fraction(v) for c, v in r.items() if v}
        while row:
            c = min(row)
            if c in pivots:
                f = row[c]
                for cc, vv in pivots[c].items():
                    nv = row.get(cc, 0) - f * vv
                    if nv:
                        row[cc] = nv
                    else:
                        row.pop(cc, None)
            else:
                inv = 1 / row[c]
                pivots[c] = {cc: vv * inv for cc, vv in row.items()}
                rank += 1
                break
    return rank


def analyse(nv, gedges, n, exact=False):
    rank = rank_exact if exact else rank_mod_p
    ends = [frozenset(e) for e in gedges]
    V = [frozenset(s) for s in itertools.combinations(range(nv), n)]
    vidx = {s: i for i, s in enumerate(V)}
    # X-edges: (P, e) with |P| = n-1 disjoint from closure of e
    E = []
    eidx = {}
    for ei, (a, b) in enumerate(gedges):
        rest = [v for v in range(nv) if v != a and v != b]
        for Pk in itertools.combinations(rest, n - 1):
            key = (frozenset(Pk), ei)
            eidx[key] = len(E)
            E.append(key)
    # union-find for hyperplane classes
    parent = list(range(len(E)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    squares = []
    for ei, fi in itertools.combinations(range(len(gedges)), 2):
        a, b = gedges[ei]
        c, d = gedges[fi]
        if len({a, b, c, d}) < 4:
            continue
        rest = [v for v in range(nv) if v not in (a, b, c, d)]
        for Qk in itertools.combinations(rest, n - 2):
            Q = frozenset(Qk)
            e1 = eidx[(Q | {c}, ei)]
            e2 = eidx[(Q | {d}, ei)]
            f1 = eidx[(Q | {a}, fi)]
            f2 = eidx[(Q | {b}, fi)]
            squares.append((Q, ei, fi, e1, e2, f1, f2))
            for x, y in ((e1, e2), (f1, f2)):
                rx, ry = find(x), find(y)
                if rx != ry:
                    parent[rx] = ry
    H = len({find(x) for x in range(len(E))})
    # connectivity of X^1
    vpar = list(range(len(V)))

    def vfind(x):
        while vpar[x] != x:
            vpar[x] = vpar[vpar[x]]
            x = vpar[x]
        return x

    for (Pk, ei) in E:
        a, b = gedges[ei]
        x, y = vfind(vidx[Pk | {a}]), vfind(vidx[Pk | {b}])
        if x != y:
            vpar[x] = y
    comps = len({vfind(x) for x in range(len(V))})
    # d2: square boundary as oriented edge chain.
    # edge (P,e) oriented a->b.  Square (Q,e=ab,f=cd): path
    # Q+a+c --(e at Q+c)--> Q+b+c --(f at Q+b)--> Q+b+d
    # back: Q+a+c --(f at Q+a)--> Q+a+d --(e at Q+d)--> Q+b+d
    d2rows = []
    Drows = []
    for (Q, ei, fi, e1, e2, f1, f2) in squares:
        d2rows.append({e1: 1, f2: 1, f1: -1, e2: -1})
        a, b = gedges[ei]
        c, d = gedges[fi]
        # delta f on e at Q+c equals delta f on e at Q+d
        r = {}
        for key, val in ((Q | {b, c}, 1), (Q | {a, c}, -1), (Q | {b, d}, -1), (Q | {a, d}, 1)):
            i = vidx[key]
            r[i] = r.get(i, 0) + val
        Drows.append(r)
    r2 = rank(d2rows, len(E))
    b1 = len(E) - (len(V) - comps) - r2
    rD = rank(Drows, len(V))
    kerD = len(V) - rD
    image = H - (kerD - comps)
    # V - E + S is the Euler characteristic of X only when n <= 2 (no 3-cubes).
    return dict(V=len(V), E=len(E), S=len(squares), comps=comps, b1=b1, H=H,
                kerD=kerD, image=image,
                euler_2skeleton=len(V) - len(E) + len(squares))


GRAPHS = {
    'triod': [(0, 1), (0, 2), (0, 3)],
    'star4': [(0, 1), (0, 2), (0, 3), (0, 4)],
    'Htree': [(0, 1), (0, 2), (0, 3), (3, 4), (3, 5)],
    'cycle3': [(0, 1), (1, 2), (2, 0)],
    'theta': [(0, 1), (0, 1), (0, 1)],
    'K4': [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)],
    'K5': [(i, j) for i in range(5) for j in range(i + 1, 5)],
    'K33': [(i, j) for i in range(3) for j in range(3, 6)],
    'lollipop': [(0, 1), (1, 2), (2, 0), (0, 3)],
    'figure8': [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)],
    'triangle_with_legs': [(0, 1), (1, 2), (2, 0), (0, 3), (1, 4), (2, 5)],
    'dumbbell': [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 5), (5, 3)],
    'theta4': [(0, 1), (0, 1), (0, 1), (0, 1)],
    # K4 with a triangle glued at a vertex / attached by a bridge: both contain
    # two disjoint cycles, so B_2 contains Z^2 and is not free.
    'K4_triangle': [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 4), (4, 5), (5, 0)],
    'K4_bridge_cycle': [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 4), (4, 5), (5, 6), (6, 4)],
}

if __name__ == '__main__':
    # usage: hyperplane_affine.py <graph> <n> [k | l1,l2,...]
    name = sys.argv[1]
    n = int(sys.argv[2])
    if len(sys.argv) > 3 and ',' in sys.argv[3]:
        k = [int(t) for t in sys.argv[3].split(',')]
    else:
        k = int(sys.argv[3]) if len(sys.argv) > 3 else max(n, 2)
    exact = os.environ.get('EXACT') == '1'
    nv, ge = subdivide(GRAPHS[name], k)
    res = analyse(nv, ge, n, exact=exact)
    ok = res['image'] == res['b1']
    print(name, 'n=%d' % n, 'k=%s' % (k,), 'field=%s' % ('Q' if exact else 'F_%d' % P),
          res, 'AFFINE' if ok else 'NOT-AFFINE')
