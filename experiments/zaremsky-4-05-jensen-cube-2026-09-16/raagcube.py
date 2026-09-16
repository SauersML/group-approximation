"""Finite convex subcomplexes of RAAG Salvetti covers, hyperplane coordinates,
and LP tests of the Jensen property (J) for the l^1 cube-complex realization.

Letters: 2*g (positive generator g) and 2*g+1 (its inverse).
Group elements are stored as lex-min reduced words (tuples of letters).
"""
import itertools, random
from fractions import Fraction

class RAAG:
    def __init__(self, n, edges):
        self.n = n
        self.comm = [[False]*n for _ in range(n)]
        for g in range(n):
            self.comm[g][g] = True
        for a, b in edges:
            self.comm[a][b] = self.comm[b][a] = True
        # maximal cliques (brute force, n small)
        cl = []
        for r in range(n, 0, -1):
            for S in itertools.combinations(range(n), r):
                if all(self.comm[a][b] for a in S for b in S):
                    if not any(set(S) <= set(T) for T in cl):
                        cl.append(S)
        self.maxcliques = cl
        self.dim = max(len(S) for S in cl)

    def normalize(self, word):
        rem = list(word)
        out = []
        while rem:
            best = None
            for i, l in enumerate(rem):
                g = l >> 1
                if all(self.comm[g][rem[j] >> 1] for j in range(i)):
                    if best is None or l < rem[best]:
                        best = i
            out.append(rem.pop(best))
        return tuple(out)

    def mul_letter(self, word, l):
        g = l >> 1
        w = list(word)
        for i in range(len(w) - 1, -1, -1):
            h = w[i] >> 1
            if h == g:
                if w[i] == l ^ 1:
                    del w[i]
                    return self.normalize(w)
                break
            if not self.comm[g][h]:
                break
        w.append(l)
        return self.normalize(w)

    def mul(self, a, b):
        for l in b:
            a = self.mul_letter(a, l)
        return a

    def inv(self, a):
        return self.normalize([l ^ 1 for l in reversed(a)])

    def dist(self, a, b):
        return len(self.mul(self.inv(a), b))

    def letters(self):
        return list(range(2 * self.n))


def ball(G, R):
    e = ()
    seen = {e}
    frontier = [e]
    for _ in range(R):
        nf = []
        for u in frontier:
            for l in G.letters():
                v = G.mul_letter(u, l)
                if v not in seen:
                    seen.add(v)
                    nf.append(v)
        frontier = nf
    return seen


def hull(G, S, cap=20000):
    """Convex hull in the median Cayley graph: close under completing squares
    and under geodesic connectivity (intervals).  We close under intervals
    between pairs by adding all vertices on geodesics (via neighbours that
    decrease distance) and under square completion; iterate to a fixpoint."""
    H = set(S)
    changed = True
    while changed:
        changed = False
        # interval closure between pairs
        Hl = list(H)
        for i in range(len(Hl)):
            for j in range(i + 1, len(Hl)):
                u, v = Hl[i], Hl[j]
                d = G.dist(u, v)
                if d <= 1:
                    continue
                # BFS layer by layer along geodesics from u to v
                layer = {u}
                for k in range(d - 1):
                    nl = set()
                    for x in layer:
                        for l in G.letters():
                            y = G.mul_letter(x, l)
                            if G.dist(y, v) == d - k - 1:
                                nl.add(y)
                    for y in nl:
                        if y not in H:
                            H.add(y)
                            changed = True
                    layer = nl
                if len(H) > cap:
                    raise RuntimeError("hull too large")
    return H


def hull_fast(G, S, cap=50000):
    """Convex hull via local convexity: a connected induced subgraph of a
    median graph is convex iff all common neighbours of its pairs at
    distance 2 lie in it.  First connect S by geodesics to S[0], then close."""
    S = list(S)
    H = set(S)
    o = S[0]
    for v in S[1:]:
        d = G.dist(o, v)
        x = o
        for k in range(d):
            for l in G.letters():
                y = G.mul_letter(x, l)
                if G.dist(y, v) == d - k - 1:
                    x = y
                    break
            H.add(x)
    todo = list(H)
    while todo:
        u = todo.pop()
        for a in G.letters():
            ua = G.mul_letter(u, a)
            # paths u - ua - uab with a,b commuting distinct gens, or u - x - u
            for b in G.letters():
                if (a >> 1) == (b >> 1) or not G.comm[a >> 1][b >> 1]:
                    continue
                ub = G.mul_letter(u, b)
                uab = G.mul_letter(ua, b)
                # pairs at distance 2 inside H: (u, uab) with common nbrs ua, ub
                if uab in H and (ua in H or ub in H):
                    for w in (ua, ub):
                        if w not in H:
                            H.add(w)
                            todo.append(w)
                # (ua, ub) at distance 2 with common neighbours u, uab
                if ua in H and ub in H:
                    for w in (u, uab):
                        if w not in H:
                            H.add(w)
                            todo.append(w)
        if len(H) > cap:
            raise RuntimeError("hull too large")
    return H


class Complex:
    """Finite convex subcomplex with hyperplane coordinates."""
    def __init__(self, G, V):
        self.G = G
        self.V = list(V)
        self.idx = {v: i for i, v in enumerate(self.V)}
        n = len(self.V)
        # edges keyed by (lower-index endpoint, letter) canonical
        self.edges = {}
        elist = []
        for v in self.V:
            for g in range(G.n):
                w = G.mul_letter(v, 2 * g)
                if w in self.idx:
                    e = (self.idx[v], self.idx[w])
                    self.edges[e] = len(elist)
                    elist.append(e)
        self.elist = elist
        parent = list(range(len(elist)))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb
        for v in self.V:
            for g in range(G.n):
                for h in range(g + 1, G.n):
                    if not G.comm[g][h]:
                        continue
                    vg = G.mul_letter(v, 2 * g)
                    vh = G.mul_letter(v, 2 * h)
                    vgh = G.mul_letter(vg, 2 * h)
                    if all(x in self.idx for x in (vg, vh, vgh)):
                        union(self.edges[(self.idx[v], self.idx[vg])], self.edges[(self.idx[vh], self.idx[vgh])])
                        union(self.edges[(self.idx[v], self.idx[vh])], self.edges[(self.idx[vg], self.idx[vgh])])
        roots = {}
        self.ehyp = []
        for i in range(len(elist)):
            r = find(i)
            if r not in roots:
                roots[r] = len(roots)
            self.ehyp.append(roots[r])
        self.nh = len(roots)
        # coordinates by BFS from V[0]
        adj = [[] for _ in range(n)]
        for i, (a, b) in enumerate(elist):
            adj[a].append((b, self.ehyp[i]))
            adj[b].append((a, self.ehyp[i]))
        coord = [None] * n
        coord[0] = 0  # bitmask as python int
        q = [0]
        while q:
            a = q.pop()
            for b, h in adj[a]:
                if coord[b] is None:
                    coord[b] = coord[a] ^ (1 << h)
                    q.append(b)
        assert all(c is not None for c in coord), "not connected"
        self.coord = coord
        self.adj = adj

    def check_isometric(self, samples=200, rng=random):
        """distance = number of separating hyperplanes, for sampled pairs"""
        for _ in range(samples):
            a, b = rng.randrange(len(self.V)), rng.randrange(len(self.V))
            d1 = self.G.dist(self.V[a], self.V[b])
            d2 = bin(self.coord[a] ^ self.coord[b]).count("1")
            if d1 != d2:
                return False
        return True

    def cubes(self):
        """All maximal-clique cubes (with all sign choices) contained in V,
        returned as (base vertex index, list of hyperplanes, signs) where the
        cube's points are base-coordinate with the listed hyperplanes free."""
        G = self.G
        out = set()
        for v in self.V:
            for C in G.maxcliques:
                for r in range(len(C), 0, -1):
                    for T in itertools.combinations(C, r):
                        for signs in itertools.product((0, 1), repeat=r):
                            corners = []
                            ok = True
                            for sub in itertools.product((0, 1), repeat=r):
                                w = v
                                for g, s, on in zip(T, signs, sub):
                                    if on:
                                        w = G.mul_letter(w, 2 * g + s)
                                if w not in self.idx:
                                    ok = False
                                    break
                                corners.append(self.idx[w])
                            if not ok:
                                continue
                            cmask = 0
                            for c in corners:
                                cmask |= self.coord[c] ^ self.coord[corners[0]]
                            base = min(self.coord[c] for c in corners)
                            # represent cube by (fixed coordinate mask outside free set, free mask)
                            fixed = self.coord[corners[0]] & ~cmask
                            out.add((fixed, cmask))
        # keep only maximal cubes
        cubes = list(out)
        maxc = []
        for (f, m) in cubes:
            dominated = False
            for (f2, m2) in cubes:
                if m2 != m and (m & m2) == m and (f & ~m2) == (f2 & ~m2) and (f2 & m) == 0:
                    dominated = True
                    break
            if not dominated:
                maxc.append((f, m))
        return maxc
