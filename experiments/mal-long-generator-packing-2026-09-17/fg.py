"""Free group F(a,b) toolkit: reduction, Stallings folding, membership, double cosets.

Letters a, b; inverses A, B.  Used by packing.py for
fpbs-mal-long-generator-packing-growth.
"""
import itertools

INV = {"a": "A", "A": "a", "b": "B", "B": "b"}
LETTERS = "aAbB"


def red(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return "".join(out)


def inv(w):
    return "".join(INV[x] for x in reversed(w))


class Folded:
    """Folded labelled graph built from based loops / paths."""

    def __init__(self, loops_at, paths=()):
        # loops_at: list of (vertex_name, word); paths: (u_name, word, v_name)
        self.n = 0
        self.names = {}
        self.edges = []
        for name, w in loops_at:
            v = self.vert(name)
            self._path(v, w, v)
        for u, w, v in paths:
            self._path(self.vert(u), w, self.vert(v))
        self._fold()

    def vert(self, name):
        if name not in self.names:
            self.names[name] = self.n
            self.n += 1
        return self.names[name]

    def _new(self):
        self.n += 1
        return self.n - 1

    def _path(self, u, w, v):
        w = red(w)
        if not w:
            self.edges.append((u, None, v))  # identify u, v
            return
        cur = u
        for i, x in enumerate(w):
            nxt = v if i == len(w) - 1 else self._new()
            if x.islower():
                self.edges.append((cur, x, nxt))
            else:
                self.edges.append((nxt, x.lower(), cur))
            cur = nxt

    def _fold(self):
        parent = list(range(self.n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(x, y):
            x, y = find(x), find(y)
            if x != y:
                parent[y] = x
                return True
            return False

        for (u, x, v) in self.edges:
            if x is None:
                union(u, v)
        changed = True
        while changed:
            changed = False
            out, inn = {}, {}
            for (u, x, v) in self.edges:
                if x is None:
                    continue
                u, v = find(u), find(v)
                for table, key, val in ((out, (u, x), v), (inn, (v, x), u)):
                    if key in table and find(table[key]) != find(val):
                        union(table[key], val)
                        changed = True
                    else:
                        table.setdefault(key, val)
        self.find = find
        self.adj = {}
        for (u, x, v) in self.edges:
            if x is None:
                continue
            u, v = find(u), find(v)
            self.adj[(u, x)] = v
            self.adj[(v, INV[x])] = u
        self.verts = {find(i) for i in range(self.n)}

    def read(self, name, w):
        cur = self.find(self.names[name])
        for x in w:
            cur = self.adj.get((cur, x))
            if cur is None:
                return None
        return cur

    def at(self, name):
        return self.find(self.names[name])


class Subgroup:
    def __init__(self, gens):
        self.gens = [red(g) for g in gens]
        self.g = Folded([("o", w) for w in self.gens])

    def contains(self, w):
        return self.g.read("o", red(w)) == self.g.at("o")

    def elements(self, L):
        """All reduced words of length <= L in the subgroup (closed reduced paths at o)."""
        o = self.g.at("o")
        res = [""]
        stack = [("", o)]
        while stack:
            w, v = stack.pop()
            if len(w) == L:
                continue
            for x in LETTERS:
                if w and w[-1] == INV[x]:
                    continue
                u = self.g.adj.get((v, x))
                if u is not None:
                    nw = w + x
                    if u == o:
                        res.append(nw)
                    stack.append((nw, u))
        return sorted(set(res), key=lambda s: (len(s), s))

    def in_double_coset(self, mid, w):
        g = Folded([("o1", x) for x in self.gens] + [("o2", x) for x in self.gens],
                   [("o1", mid, "o2")])
        return g.read("o1", red(w)) == g.at("o2")

    def generates_F2_with(self, t):
        g = Folded([("o", w) for w in self.gens + [red(t)]])
        o = g.at("o")
        return len(g.verts) == 1 and (o, "a") in g.adj and (o, "b") in g.adj


def reduced_words(L):
    for n in range(1, L + 1):
        for tup in itertools.product(LETTERS, repeat=n):
            w = "".join(tup)
            if red(w) == w:
                yield w
