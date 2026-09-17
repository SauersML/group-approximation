"""dim H^1 of the level-k block cochain complex of a 2-graph (evidence for cocycle rigidity).

For a row-finite 2-graph given by tiles, colour-1/colour-2 edges and squares, a locally
constant real cocycle on the path groupoid G_Lambda is a pair (phi_1, phi_2) of locally
constant functions on the infinite path space with
    phi_1(x) + phi_2(sigma_1 x) = phi_2(x) + phi_1(sigma_2 x),
modulo coboundaries (h o sigma_1 - h, h o sigma_2 - h).  H^1(G_Lambda; R) is the colimit
over k of H^1 of the finite complex
    C^0_k = R^{(k,k)-blocks}  ->  C^1_k = R^{(k+1,k)-blocks} + R^{(k,k+1)-blocks}
          ->  C^2_k = R^{(k+1,k+1)-blocks},
where an (a,b)-block is the grid t[i][j], 0<=i<=a, 0<=j<=b, of the first a colour-1 and
b colour-2 steps of a path.  Level 0 is the square complex K(Lambda) of certificate.py.

Upper bound: dim H^1 <= dim C^1 - rank_GF(p) delta_1 - (dim C^0 - #components), since
rank over GF(p) <= rank over Q and rank delta_0 = dim C^0 - #components exactly.
Lower bound 2: d_1 = (1,0) and d_2 = (0,1) are independent in every level and in the
colimit (Birkhoff sums of a coboundary along sigma_1^N sigma_2^M are bounded).
"""
import json, sys, time, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "nv-brick-coding-2026-09-17"))
import rs2graph, tp
from certificate import rank_mod_p


def grids(tiles, E1, E2, sq, a, b):
    """All (a,b)-blocks as tuples of rows: block[i][j] = t_{i,j}."""
    out1, out2 = {}, {}
    for (s, t) in E1:
        out1.setdefault(s, []).append(t)
    for (s, t) in E2:
        out2.setdefault(s, []).append(t)
    sqset = set()
    for (e, f, f2, e2) in sq:
        t00, t10 = E1[e]
        t11 = E2[f][1]
        t01 = E2[f2][1]
        sqset.add((t00, t10, t01, t11))
    # start with (a,0)-blocks: colour-1 paths
    rows = [(t,) for t in range(len(tiles))]
    for _ in range(a):
        rows = [r + (u,) for r in rows for u in out1.get(r[-1], [])]
    blocks = [(r,) for r in rows]  # block = tuple of columns-in-j; block[j] = row (t_{0,j},...,t_{a,j})
    for _ in range(b):
        new = []
        for B in blocks:
            prev = B[-1]
            partial = [(u,) for u in out2.get(prev[0], [])]
            for i in range(1, a + 1):
                partial = [p + (u,) for p in partial for u in out1.get(p[-1], [])
                           if (prev[i - 1], prev[i], p[-1], u) in sqset]
            new.extend(B + (p,) for p in partial)
        blocks = new
    # convert to block[i][j]
    return [tuple(tuple(B[j][i] for j in range(b + 1)) for i in range(a + 1)) for B in blocks]


def sub(B, i0, i1, j0, j1):
    return tuple(tuple(B[i][j0:j1 + 1]) for i in range(i0, i1 + 1))


def h1_level(tiles, E1, E2, sq, k):
    V = grids(tiles, E1, E2, sq, k, k)
    A1 = grids(tiles, E1, E2, sq, k + 1, k)
    A2 = grids(tiles, E1, E2, sq, k, k + 1)
    F = grids(tiles, E1, E2, sq, k + 1, k + 1)
    iv = {B: n for n, B in enumerate(V)}
    i1 = {B: n for n, B in enumerate(A1)}
    i2 = {B: len(A1) + n for n, B in enumerate(A2)}
    # components of delta_0 graph
    par = list(range(len(V)))

    def fd(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for B in A1:
        par[fd(iv[sub(B, 0, k, 0, k)])] = fd(iv[sub(B, 1, k + 1, 0, k)])
    for B in A2:
        par[fd(iv[sub(B, 0, k, 0, k)])] = fd(iv[sub(B, 0, k, 1, k + 1)])
    comps = len({fd(x) for x in range(len(V))})
    rows = []
    for B in F:
        r = {}
        for c, s in ((i1[sub(B, 0, k + 1, 0, k)], 1), (i2[sub(B, 1, k + 1, 0, k + 1)], 1),
                     (i2[sub(B, 0, k, 0, k + 1)], -1), (i1[sub(B, 0, k + 1, 1, k + 1)], -1)):
            r[c] = r.get(c, 0) + s
        rows.append({c: x for c, x in r.items() if x})
    r1 = rank_mod_p(rows, len(A1) + len(A2))
    h1 = len(A1) + len(A2) - r1 - (len(V) - comps)
    return dict(k=k, V=len(V), E=len(A1) + len(A2), F=len(F), components=comps, rank1=r1, h1_upper=h1)


def cells(tiles, E1, E2, sq, k):
    V = grids(tiles, E1, E2, sq, k, k)
    A1 = grids(tiles, E1, E2, sq, k + 1, k)
    A2 = grids(tiles, E1, E2, sq, k, k + 1)
    F = grids(tiles, E1, E2, sq, k + 1, k + 1)
    iv = {B: n for n, B in enumerate(V)}
    i1 = {B: n for n, B in enumerate(A1)}
    i2 = {B: len(A1) + n for n, B in enumerate(A2)}
    edges = [(iv[sub(B, 0, k, 0, k)], iv[sub(B, 1, k + 1, 0, k)]) for B in A1]
    edges += [(iv[sub(B, 0, k, 0, k)], iv[sub(B, 0, k, 1, k + 1)]) for B in A2]
    rels = [((i1[sub(B, 0, k + 1, 0, k)], 1), (i2[sub(B, 1, k + 1, 0, k + 1)], 1),
             (i2[sub(B, 0, k, 0, k + 1)], -1), (i1[sub(B, 0, k + 1, 1, k + 1)], -1)) for B in F]
    return len(V), edges, rels


def h1_fast(nV, edges, rels):
    """Upper bound for dim H^1 (exact over GF(p)), same quantity as h1_level.

    Gauge-fix a spanning tree to 0 (each class has a unique such representative when the
    1-skeleton is connected), propagate 1-term relations (x = 0) and 2-term relations
    with unit coefficients (x = +-y) by a signed union-find, and finish the remaining
    relations with elimination over GF(p).  Every step is an exact linear substitution."""
    par = list(range(nV))

    def fv(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    ZERO = len(edges)
    up = list(range(len(edges) + 1))
    sg = [1] * (len(edges) + 1)
    ncomp = nV
    for e, (a, b) in enumerate(edges):
        ra, rb = fv(a), fv(b)
        if ra != rb:
            par[ra] = rb
            ncomp -= 1
            up[e] = ZERO
    assert ncomp == 1

    def fe(x):
        s = 1
        path = []
        while up[x] != x:
            path.append(x)
            s *= sg[x]
            x = up[x]
        acc = s
        for y in path:
            t = sg[y]
            up[y] = x
            sg[y] = acc
            acc *= t
        return x, s

    def reduce(rel):
        terms = {}
        for (e, c) in rel:
            r, s = fe(e)
            if r != ZERO:
                terms[r] = terms.get(r, 0) + c * s
        return {r: c for r, c in terms.items() if c}
    active = list(rels)
    changed = True
    while changed:
        changed = False
        rest = []
        for rel in active:
            terms = reduce(rel)
            if not terms:
                continue
            if len(terms) == 1:  # c x = 0 with 0 < |c| <= 4
                (r, c), = terms.items()
                up[r], sg[r] = ZERO, 1
                changed = True
            elif len(terms) == 2 and all(abs(c) == 1 for c in terms.values()):
                (r1, c1), (r2, c2) = terms.items()
                up[r1], sg[r1] = r2, -c2 * c1   # x1 = -(c2/c1) x2
                changed = True
            else:
                rest.append(rel)
        active = rest
    roots = {}
    for e in range(len(edges)):
        r, s = fe(e)
        if r != ZERO and r not in roots:
            roots[r] = len(roots)
    rows = []
    for rel in active:
        t = reduce(rel)
        if t:
            rows.append({roots[r]: c for r, c in t.items()})
    rk = rank_mod_p(rows, len(roots))
    return dict(V=nV, E=len(edges), F=len(rels), free_after_propagation=len(roots),
                remaining_relations=len(rows), h1_upper=len(roots) - rk)
