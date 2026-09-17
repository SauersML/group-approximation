#!/usr/bin/env python3
"""Stage coset graph of Gamma_mal as a nerve of hull translates.

Setting.  H = <a, b> with b = s a s^-2, a subgroup of F = F(a, s).  This is
the stage pair (H_n, H_{n+1}) of Gamma_mal with s = b_{n+1}.

Coset graph Cos.  Vertices: left cosets gH.  Edges: one edge per element
k of F, joining kH and k s^-1 H.  (Inverting, this is the class graph of
E_H v Theta for a free action, Theta = s-edges on a set B: the right coset
H gamma is joined to H s gamma through the edge gamma, open iff gamma x in B.)

Tree picture.  T = right Cayley tree of F on {a, s}; F acts on the left.
T_H = hull of H = vertices readable in the Stallings core from v0.  Its
vertex set is V = H u Hs u Hsa (the three core vertices).  The script checks:

  (N1) every vertex p of T lies in exactly three translates of T_H, namely
       pH, p s^-1 H, p a^-1 s^-1 H (by the formula k in p V^-1);
  (N2) two distinct translates meet iff they are adjacent in Cos, and the
       edge element is determined by the pair (malnormality);
  (N3) D = max number of vertices of the intersection of two distinct
       translates (computed on a ball);
  (C)  counts of simple paths from X = T_H to Y = s^-1 T_H in Cos minus
       the edge e = element 1, by length, on the nerve of translates meeting
       a ball of radius R; stabilization in R is reported.

Letters: a = 1, A = -1, s = 2, S = -2.
"""

import sys
from collections import defaultdict, deque

A_, S_ = 1, 2
LET = [1, -1, 2, -2]


def reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def inv(w):
    return tuple(-x for x in reversed(w))


def mul(*ws):
    out = []
    for w in ws:
        for x in w:
            if out and out[-1] == -x:
                out.pop()
            else:
                out.append(x)
    return tuple(out)


# Stallings core of H: v0 -a-> v0, v0 -s-> v1, v1 -a-> v2, v1 -s-> v2.
EDGES = [(0, 1, 0), (0, 2, 1), (1, 1, 2), (1, 2, 2)]
FWD = {}
BWD = {}
for (u, x, v) in EDGES:
    FWD[(u, x)] = v
    BWD[(v, x)] = u


def step(q, x):
    if x > 0:
        return FWD.get((q, x))
    return BWD.get((q, -x))


def read(w, q=0):
    """Read reduced w from q; return (state, index where stuck or len(w))."""
    for i, x in enumerate(w):
        r = step(q, x)
        if r is None:
            return q, i
        q = r
    return q, len(w)


def in_H(w):
    w = reduce(w)
    q, i = read(w)
    return i == len(w) and q == 0


def in_hull(w):
    """w reduced; vertex w of T lies in T_H."""
    q, i = read(w)
    return i == len(w)


def coset_key(k):
    """Canonical key of the left coset kH, via the right coset H k^-1."""
    w = inv(reduce(k))
    q, i = read(w)
    return (q, w[i:])


def ball(R):
    verts = [()]
    frontier = [()]
    for _ in range(R):
        nf = []
        for w in frontier:
            for x in LET:
                if w and w[-1] == -x:
                    continue
                v = w + (x,)
                nf.append(v)
        verts.extend(nf)
        frontier = nf
    return verts


A = (A_,)
Ai = (-A_,)
S = (S_,)
Si = (-S_,)
B = mul(S, A, Si, Si)


def translates_at(p):
    return [coset_key(p), coset_key(mul(p, Si)), coset_key(mul(p, Ai, Si))]


def checks():
    assert in_H(A) and in_H(B)
    assert not in_H(S)
    # malnormality spot check on short words
    short = ball(6)
    Hshort = [w for w in short if in_H(w)]
    bad = 0
    for g in short:
        if in_H(g):
            continue
        for h in Hshort:
            if h and in_H(mul(inv(g), h, g)) and len(mul(inv(g), h, g)) <= 6:
                bad += 1
    print("malnormality spot check violations (|g|,|h|<=6):", bad)
    # (N1) at each vertex, exactly three translates contain it, checked by
    # testing k^-1 p in hull for the three k, and distinctness
    for p in ball(5):
        ks = [p, mul(p, Si), mul(p, Ai, Si)]
        keys = {coset_key(k) for k in ks}
        assert len(keys) == 3, p
        for k in ks:
            assert in_hull(mul(inv(k), p)), (p, k)
    print("N1 ok on ball(5): three distinct translates at each vertex")


def pullback_components():
    """Off-diagonal part of the Stallings pullback core x core.

    Malnormality certificate: every off-diagonal component is a tree.  The
    largest component size bounds |T_H cap k T_H| for kH != H (the map
    p -> (state of p, state of k^-1 p) is injective on the intersection).
    """
    verts = [(i, j) for i in range(3) for j in range(3) if i != j]
    edges = []
    for (u, x, v) in EDGES:
        for (u2, x2, v2) in EDGES:
            if x == x2 and u != u2 and v != v2:
                edges.append(((u, u2), (v, v2)))
    # union-find
    parent = {v: v for v in verts}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for (p, q) in edges:
        parent[find(p)] = find(q)
    comps = defaultdict(list)
    for v in verts:
        comps[find(v)].append(v)
    for r, vs in comps.items():
        ne = sum(1 for (p, q) in edges if find(p) == r)
        print(f"pullback off-diagonal component {sorted(vs)}: {len(vs)} vertices, "
              f"{ne} edges, tree={ne == len(vs) - 1}")
    # also check no edge joins diagonal to off-diagonal (automatic for folded
    # graphs) and each tree edge of T lies in exactly two translates:
    outs = defaultdict(int)
    for (u, x, v) in EDGES:
        outs[x] += 1
    print("translates containing a T-edge labelled a, s:", outs[1], outs[2])


def build(R):
    verts = ball(R)
    members = defaultdict(set)  # translate key -> vertices in ball
    at = {}
    for p in verts:
        ts = translates_at(p)
        at[p] = ts
        for t in ts:
            members[t].add(p)
    # nerve adjacency with edge element identification
    adj = defaultdict(set)
    edge_el = {}
    conflicts = 0
    for p in verts:
        t0, t1, t2 = at[p]
        # pair types: (pH, p s^-1 H) edge element p; (p s^-1 H, p a^-1 s^-1 H)
        # element p s^-1; (pH, p a^-1 s^-1 H) element p a^-1
        for (u, v, el) in [(t0, t1, p), (t1, t2, mul(p, Si)), (t0, t2, mul(p, Ai))]:
            key = frozenset((u, v))
            # canonical edge id: edge element k joins kH and k s^-1 H
            if key in edge_el:
                if edge_el[key] != el:
                    conflicts += 1
            else:
                edge_el[key] = el
            adj[u].add(v)
            adj[v].add(u)
    return verts, members, adj, edge_el, conflicts


def intersection_stats(members, R):
    """Max |T_H cap kT_H| over translates meeting T_H inside the ball."""
    X = coset_key(())
    MX = members[X]
    best = 0
    hist = defaultdict(int)
    for t, M in members.items():
        if t == X:
            continue
        c = len(MX & M)
        if c:
            hist[c] += 1
            best = max(best, c)
    return best, dict(hist)


def count_paths(adj, X, Y, maxlen, forbid_edge):
    # BFS distance to Y in graph minus forbidden edge
    fu, fv = forbid_edge
    dist = {Y: 0}
    dq = deque([Y])
    while dq:
        u = dq.popleft()
        if dist[u] >= maxlen:
            continue
        for v in adj[u]:
            if {u, v} == {fu, fv}:
                continue
            if v not in dist:
                dist[v] = dist[u] + 1
                dq.append(v)
    counts = defaultdict(int)
    path = [X]
    onpath = {X}

    def dfs(u, L):
        for v in adj[u]:
            if {u, v} == {fu, fv}:
                continue
            if v in onpath:
                continue
            dv = dist.get(v)
            if dv is None or L + 1 + dv > maxlen:
                continue
            if v == Y:
                counts[L + 1] += 1
                continue
            onpath.add(v)
            path.append(v)
            dfs(v, L + 1)
            path.pop()
            onpath.discard(v)

    dfs(X, 0)
    return dict(sorted(counts.items()))


def main():
    # arguments: R:maxlen pairs, e.g. 8:5 10:6
    specs = [tuple(int(y) for y in x.split(":")) for x in sys.argv[1:]] or [(4, 5), (6, 5), (8, 5)]
    checks()
    pullback_components()
    X = coset_key(())
    Y = coset_key(Si)
    for R, maxlen in specs:
        verts, members, adj, edge_el, conflicts = build(R)
        best, hist = intersection_stats(members, R)
        print(f"R={R}: vertices {len(verts)}, translates {len(members)}, "
              f"nerve edges {len(edge_el)}, edge-element conflicts {conflicts}")
        print(f"  |T_H cap kT_H| histogram over neighbours of T_H: {hist}; max {best}")
        print(f"  |T_H cap s^-1 T_H| in ball: {sorted(members[X] & members[Y])}")
        print(f"  deg(X) in ball: {len(adj[X])}")
        c = count_paths(adj, X, Y, maxlen, (X, Y))
        print(f"  simple X-Y paths avoiding e, by length (<= {maxlen}): {c}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
