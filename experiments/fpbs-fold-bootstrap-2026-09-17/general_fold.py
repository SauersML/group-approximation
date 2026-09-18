#!/usr/bin/env python3
"""General Stallings-fold seeding for K = <a, w> <= F_2 on a finite quotient Q.

Labels: 0=a, 1=b, 2=a^-1, 3=b^-1.  A graph over Cay(Q) is folded with
union-find.  A seed identifies two vertices in one fiber (cost 1/|Q| in the
measured relation).  We count seeds until every fiber is one class, i.e. the
folded pullback is Cay(Q).  Seeds/|Q| upper-bounds relC(R_L;R_K) for every
free action of L with an equivariant factor map onto Q.
"""
import random
import sys

INV = [2, 3, 0, 1]


class Folder:
    def __init__(self, nv):
        self.par = list(range(nv))
        self.adj = [[-1] * nv for _ in range(4)]
        self.merges = 0

    def find(self, x):
        par = self.par
        r = x
        while par[r] != r:
            r = par[r]
        while par[x] != r:
            par[x], x = r, par[x]
        return r

    def add_edge(self, u, s, v):
        """Add u -s-> v (and the inverse); fold if needed."""
        self._link(u, s, v)
        self._link(v, INV[s], u)

    def _link(self, u, s, v):
        ru = self.find(u)
        t = self.adj[s][ru]
        if t == -1:
            self.adj[s][ru] = v
        else:
            self.union(t, v)

    def union(self, x, y):
        stack = [(x, y)]
        adj = self.adj
        while stack:
            x, y = stack.pop()
            rx, ry = self.find(x), self.find(y)
            if rx == ry:
                continue
            self.par[ry] = rx
            self.merges += 1
            self.on_merge(rx, ry)
            for s in range(4):
                ty = adj[s][ry]
                if ty != -1:
                    tx = adj[s][rx]
                    if tx == -1:
                        adj[s][rx] = ty
                    else:
                        stack.append((tx, ty))

    def on_merge(self, rx, ry):
        pass


def reduce_word(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return out


def phi_word(w):
    """phi(a) = a, phi(b) = b a b^-1 b^-1."""
    img = {0: [0], 2: [2], 1: [1, 0, 3, 3], 3: [1, 1, 2, 3]}
    out = []
    for x in w:
        out.extend(img[x])
    return reduce_word(out)


def stallings(gens):
    """Folded Stallings graph of <gens>; returns (num vertices, edge list)."""
    edges = []
    nv = 1
    for w in gens:
        prev = 0
        for i, s in enumerate(w):
            if i == len(w) - 1:
                nxt = 0
            else:
                nxt = nv
                nv += 1
            edges.append((prev, s, nxt))
            prev = nxt
    f = Folder(nv)
    for (u, s, v) in edges:
        f.add_edge(u, s, v)
    reps = sorted({f.find(x) for x in range(nv)})
    ren = {r: i for i, r in enumerate(reps)}
    out = set()
    for s in (0, 1):
        for r in reps:
            t = f.adj[s][r]
            if t != -1:
                out.add((ren[r], s, ren[f.find(t)]))
    base = ren[f.find(0)]
    # renumber so that base is 0
    perm = {base: 0, 0: base} if base != 0 else {}
    fix = (lambda x: perm.get(x, x))
    return len(reps), sorted((fix(u), s, fix(v)) for (u, s, v) in out)


class Pullback(Folder):
    def __init__(self, V, edges, ra, rb):
        n = len(ra)
        self.n, self.V = n, V
        super().__init__(V * n)
        self.fib = [V] * n
        self.classes = V * n
        tabs = (ra, rb)
        for (u, s, v) in edges:
            t = tabs[s]
            for q in range(n):
                self.add_edge(u * n + q, s, v * n + t[q])
        assert self.merges == 0, "pullback of a folded graph must be an immersion"

    def on_merge(self, rx, ry):
        self.fib[rx % self.n] -= 1
        self.classes -= 1

    def seed(self, q, rng):
        n = self.n
        r0 = self.find(q)
        others = [v * n + q for v in range(1, self.V) if self.find(v * n + q) != r0]
        self.union(q, rng.choice(others))


def run_seeding(V, edges, ra, rb, rng, mode):
    P = Pullback(V, edges, ra, rb)
    n = P.n
    seeds = 0
    order = list(range(n))
    rng.shuffle(order)
    if mode == "random":
        ptr = 0
        while P.classes > n:
            while P.fib[order[ptr]] == 1:
                ptr += 1
            P.seed(order[ptr], rng)
            seeds += 1
    else:  # "lowest": seed in a fiber with the fewest (>1) classes
        buckets = [[] for _ in range(V + 1)]
        for q in order:
            buckets[V].append(q)
        while P.classes > n:
            done = False
            for c in range(2, V + 1):
                b = buckets[c]
                while b:
                    k = rng.randrange(len(b))
                    q = b[k]
                    b[k] = b[-1]
                    b.pop()
                    fc = P.fib[q]
                    if fc == c:
                        P.seed(q, rng)
                        seeds += 1
                        if P.fib[q] > 1:
                            buckets[P.fib[q]].append(q)
                        done = True
                        break
                    elif fc > 1:
                        buckets[fc].append(q)
                if done:
                    break
            # refresh: fibers whose count dropped are re-bucketed lazily
            if done and rng.random() < 0.02:
                for c in range(2, V + 1):
                    buckets[c] = []
                for q in range(n):
                    if P.fib[q] > 1:
                        buckets[P.fib[q]].append(q)
    return seeds
