"""Exhaustive search for integral anti-flag realizations of a fixed girth-5 graph.

Target: the Robertson graph (the unique (4,5)-cage: 19 vertices, 4-regular,
girth 5), whose right-angled Coxeter group has chi = 1 - 19/2 + 38/4 = 1 > 0.

A faithful rho: W -> GL_3(Z), in normal form, sends s_v to I - (2/d) p_v L_v^T.
The necessary conditions used here are all proved in
sl3z-racg-witnesses-are-antiflag-configurations:
  - (A2) u ~ v  <=>  L_u.p_v = 0 and L_v.p_u = 0;
  - (A3) for u !~ v: a_uv a_vu not in {1,2,3};
  - distinct centres and distinct axes. For girth >= 5 and min degree >= 2 this
    follows from (R2): if p_u = p_w, all neighbours of u are neighbours of w, so
    there is a 4-cycle. (R3) gives the dual statement.
The search is exhaustive over all anti-flags with entries in [-B, B]. Vertex 0
is fixed up to the signed-permutation group, which preserves the box.

usage: exact.py B [graph]    graph in {robertson, rob17} (default robertson)
"""
import itertools, sys, time
import numpy as np
import antiflag as AF

ROBERTSON = [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (1, 7), (2, 8), (2, 9), (2, 10),
             (3, 11), (3, 12), (3, 13), (4, 14), (4, 15), (4, 16), (5, 8), (5, 11), (5, 14),
             (6, 9), (6, 15), (6, 18), (7, 12), (7, 16), (7, 17), (8, 12), (8, 15), (9, 11),
             (9, 17), (10, 13), (10, 16), (10, 18), (11, 16), (12, 18), (13, 15), (13, 17),
             (14, 17), (14, 18)]


def girth(n, E):
    A = [set() for _ in range(n)]
    for u, v in E:
        A[u].add(v); A[v].add(u)
    g = 10 ** 9
    for s in range(n):
        dist = {s: 0}; par = {s: -1}; q = [s]
        for x in q:
            for y in A[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; par[y] = x; q.append(y)
                elif par[x] != y:
                    g = min(g, dist[x] + dist[y] + 1)
    return g, A


def main():
    B = int(sys.argv[1]); name = sys.argv[2] if len(sys.argv) > 2 else 'robertson'
    if name == 'robertson':
        E = ROBERTSON; n = 19
        g, Adj = girth(n, E)
        assert g == 5 and all(len(a) == 4 for a in Adj), (g,)
    elif name == 'rob17':
        # Robertson minus the adjacent vertices 0 and 1: 17 vertices, 31 edges, chi = 1/4
        keep = list(range(2, 19)); rl = {v: i for i, v in enumerate(keep)}
        E = [(rl[u], rl[v]) for u, v in ROBERTSON if u in rl and v in rl]; n = 17
        g, Adj = girth(n, E)
        assert g >= 5 and len(E) == 31 and min(len(a) for a in Adj) >= 3, (g, len(E))
        print("chi*4 =", 4 - 2 * n + len(E), flush=True)
    else:
        raise SystemExit("unknown graph " + name)
    V = AF.build(B); N = len(V)
    P = np.array([x[0] for x in V], dtype=np.int64)
    L = np.array([x[1] for x in V], dtype=np.int64)
    d = np.array([x[2] for x in V], dtype=np.int64)
    D = L @ P.T                       # D[x, y] = L_x . p_y
    Z = (D == 0)
    MUT = Z & Z.T                     # mutual incidence = edge
    pr4 = 4 * D * D.T                 # a_xy a_yx * d_x d_y
    dd = np.outer(d, d)
    fin = np.zeros_like(MUT)
    for k in (1, 2, 3):
        fin |= (pr4 == k * dd)
    cid = {}; aid = {}
    cidx = np.array([cid.setdefault(tuple(x[0]), len(cid)) for x in V])
    aidx = np.array([aid.setdefault(tuple(x[1]), len(aid)) for x in V])
    same = (cidx[:, None] == cidx[None, :]) | (aidx[:, None] == aidx[None, :])
    NONOK = ~MUT & ~fin & ~same       # allowed for a non-edge
    del D, Z, pr4, dd, fin, same
    print("B", B, "antiflags", N, "graph", name, flush=True)

    # BFS order
    order = [0]
    for x in order:
        for y in sorted(Adj[x]):
            if y not in order:
                order.append(y)
    pos = {v: i for i, v in enumerate(order)}

    # vertex 0 up to signed permutations
    G = []
    for perm in itertools.permutations(range(3)):
        for sg in itertools.product((1, -1), repeat=3):
            M = np.zeros((3, 3), dtype=np.int64)
            for i in range(3):
                M[i, perm[i]] = sg[i]
            G.append(M)
    index = {(tuple(x[0]), tuple(x[1])): i for i, x in enumerate(V)}

    def canon_key(i):
        best = None
        for M in G:
            p = M @ P[i]; l = M @ L[i]      # M orthogonal: L.p preserved
            nz = next(c for c in p if c != 0)
            if nz < 0:
                p = -p; l = -l
            key = (tuple(p), tuple(l))
            if best is None or key < best:
                best = key
        return best

    roots = sorted({canon_key(i) for i in range(N)})
    roots = [index[k] for k in roots]
    print("root orbits", len(roots), flush=True)

    assign = [-1] * n
    stats = {'nodes': 0, 'sol': 0, 'depth': [0] * (n + 1)}
    t0 = time.time()

    # forward checking with minimum-remaining-values ordering: masks[w] is the
    # set of anti-flags still compatible with every assigned vertex
    def rec(k, masks):
        stats['nodes'] += 1; stats['depth'][k] += 1
        if k == n:
            stats['sol'] += 1
            print("SOLUTION", [V[assign[v]] for v in range(n)], flush=True)
            return
        free = [w for w in range(n) if assign[w] < 0]
        counts = masks[free].sum(axis=1)
        if counts.min() == 0:
            return
        # prefer vertices with an assigned neighbour, then fewest candidates
        key = [(0 if any(assign[u] >= 0 for u in Adj[w]) else 1, int(c), w) for w, c in zip(free, counts)]
        v = min(key)[2]
        for c in np.nonzero(masks[v])[0]:
            assign[v] = int(c)
            nm = masks.copy()
            for w in free:
                if w != v:
                    nm[w] &= MUT[c] if w in Adj[v] else NONOK[c]
            rec(k + 1, nm)
        assign[v] = -1

    for r in roots:
        assign[0] = r
        masks = np.ones((n, N), dtype=bool)
        for w in range(1, n):
            masks[w] &= MUT[r] if w in Adj[0] else NONOK[r]
        rec(1, masks)
        print("root", V[r], "cumulative nodes", stats['nodes'], "solutions", stats['sol'],
              "%.1fs" % (time.time() - t0), flush=True)
    print("nodes", stats['nodes'], "solutions", stats['sol'],
          "max depth reached", max(i for i, c in enumerate(stats['depth']) if c),
          "depth profile", stats['depth'], "time %.1fs" % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
