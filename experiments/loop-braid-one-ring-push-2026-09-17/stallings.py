#!/usr/bin/env python3
"""Stallings graphs for finitely generated subgroups of F_n.

Words are tuples of nonzero ints (i = x_i, -i = x_i^{-1}), as in
experiments/loop-braid-bfmwz-push-2026-09-17/mutual_link.py.

  Graph(gens)          folded Stallings graph of <gens>, base vertex 0
  g.contains(word)     membership test
  g.rank()             rank of the subgroup
  intersect(g, h)      folded graph of the intersection (pullback, base component)
"""


class Graph:
    def __init__(self, gens=(), n=None):
        self.adj = {0: {}}          # v -> {signed letter: v'}
        self.next = 1
        for w in gens:
            self.add_loop(w)
        self.fold()

    # ------------------------------------------------------------ construction
    def new_vertex(self):
        v = self.next
        self.next += 1
        self.adj[v] = {}
        return v

    def add_edge(self, u, x, v):
        # stores both directions; folding resolves collisions later
        self.adj[u].setdefault(x, [])
        self.adj[v].setdefault(-x, [])
        if isinstance(self.adj[u][x], list):
            self.adj[u][x].append(v)
        if isinstance(self.adj[v][-x], list):
            self.adj[v][-x].append(u)

    def add_loop(self, w):
        if not w:
            return
        u = 0
        for k, x in enumerate(w):
            v = 0 if k == len(w) - 1 else self.new_vertex()
            self.add_edge(u, x, v)
            u = v

    def fold(self):
        """Fold with union-find. After this, adj[v][x] is a single vertex."""
        parent = {}

        def find(a):
            while parent.get(a, a) != a:
                parent[a] = parent.get(parent[a], parent[a])
                a = parent[a]
            return a

        # edge multiset: list of (u, x, v) with x > 0
        edges = []
        for u, d in self.adj.items():
            for x, vs in d.items():
                if x > 0:
                    for v in (vs if isinstance(vs, list) else [vs]):
                        edges.append((u, x, v))
        changed = True
        while changed:
            changed = False
            out = {}
            for (u, x, v) in edges:
                u, v = find(u), find(v)
                for key, tgt in (((u, x), v), ((v, -x), u)):
                    if key in out:
                        t = find(out[key])
                        if t != tgt:
                            a, b = sorted((t, tgt))
                            parent[b] = a
                            changed = True
                    else:
                        out[key] = tgt
            edges = [(find(u), x, find(v)) for (u, x, v) in edges]
        verts = {find(v) for v in self.adj}
        verts.add(find(0))
        adj = {v: {} for v in verts}
        for (u, x, v) in set(edges):
            adj[u][x] = v
            adj[v][-x] = u
        # relabel so that the base is 0
        b = find(0)
        lab = {b: 0}
        for v in sorted(verts):
            if v not in lab:
                lab[v] = len(lab)
        self.adj = {lab[v]: {x: lab[t] for x, t in d.items()} for v, d in adj.items()}
        self.next = len(lab)
        self.trim()

    def trim(self):
        """Remove hanging trees not containing the base (keeps the core plus base path)."""
        while True:
            leaves = [v for v, d in self.adj.items() if v != 0 and len(d) <= 1]
            if not leaves:
                return
            for v in leaves:
                for x, t in list(self.adj[v].items()):
                    del self.adj[t][-x]
                del self.adj[v]

    # ------------------------------------------------------------ queries
    def contains(self, w):
        v = 0
        for x in w:
            if x not in self.adj[v]:
                return False
            v = self.adj[v][x]
        return v == 0

    def rank(self):
        V = len(self.adj)
        E = sum(1 for d in self.adj.values() for x in d if x > 0)
        return E - V + 1

    def size(self):
        return len(self.adj)

    def basis(self):
        """Free basis read off a BFS spanning tree (one word per non-tree edge)."""
        path = {0: ()}
        order = [0]
        tree = set()
        for u in order:
            for x, t in sorted(self.adj[u].items()):
                if t not in path:
                    path[t] = path[u] + (x,)
                    tree.add((u, x, t))
                    tree.add((t, -x, u))
                    order.append(t)
        out = []
        for u, d in self.adj.items():
            for x, t in sorted(d.items()):
                if x > 0 and (u, x, t) not in tree:
                    w = list(path[u]) + [x] + [-y for y in reversed(path[t])]
                    red = []
                    for y in w:
                        if red and red[-1] == -y:
                            red.pop()
                        else:
                            red.append(y)
                    out.append(tuple(red))
        return out


def intersect(g, h):
    """Stallings graph of the intersection (component of (0,0) in the pullback)."""
    start = (0, 0)
    idx = {start: 0}
    stack = [start]
    edges = set()
    while stack:
        p = stack.pop()
        a, b = p
        for x, ta in g.adj[a].items():
            if x in h.adj[b]:
                q = (ta, h.adj[b][x])
                if q not in idx:
                    idx[q] = len(idx)
                    stack.append(q)
                if x > 0:
                    edges.add((idx[p], x, idx[q]))
                else:
                    edges.add((idx[q], -x, idx[p]))
    out = Graph()
    out.adj = {i: {} for i in range(len(idx))}
    for (u, x, v) in edges:
        out.adj[u][x] = v
        out.adj[v][-x] = u
    out.next = len(idx)
    out.trim()
    return out


if __name__ == '__main__':
    # self-test
    g = Graph([(1, 2), (3,)])
    assert g.rank() == 2 and g.contains((1, 2, 3, -2, -1)) and not g.contains((1,))
    h = Graph([(1,), (2, 3)])
    i = intersect(g, h)
    print('rank <x1x2,x3> cap <x1,x2x3> =', i.rank())
    f = Graph([(1, 1), (1, 1, 1)])
    assert f.rank() == 1 and f.contains((1,))
    print('stallings self-test ok')
