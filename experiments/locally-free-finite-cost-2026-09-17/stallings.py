"""Minimal Stallings-folding toolkit for F(a,c).  Letters: a,c; inverses A,C.

Used to count two-letter absorption certificates for the step
Delta_0 = <a, c a c^-2>  <=  Delta_1 = <a, c>   (one stage of Gamma_mal).
"""
import itertools

INV = {"a": "A", "A": "a", "c": "C", "C": "c"}


def reduce(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return "".join(out)


def inv(w):
    return "".join(INV[x] for x in reversed(w))


class Graph:
    """Labelled graph; edges stored as dict (v, letter) -> set(v') for positive letters
    and their inverses. Folding via union-find."""

    def __init__(self):
        self.n = 0
        self.edges = []  # (u, x, v) with x in {a, c}

    def new(self):
        self.n += 1
        return self.n - 1

    def add_path(self, u, word, v):
        cur = u
        for i, x in enumerate(word):
            nxt = v if i == len(word) - 1 else self.new()
            if x.islower():
                self.edges.append((cur, x, nxt))
            else:
                self.edges.append((nxt, x.lower(), cur))
            cur = nxt

    def fold(self):
        parent = list(range(self.n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        changed = True
        while changed:
            changed = False
            out, inn = {}, {}
            for (u, x, v) in self.edges:
                u, v = find(u), find(v)
                for table, key, val in ((out, (u, x), v), (inn, (v, x), u)):
                    if key in table and find(table[key]) != find(val):
                        parent[find(val)] = find(table[key])
                        changed = True
                    else:
                        table.setdefault(key, val)
        self.find = find
        self.adj = {}
        for (u, x, v) in self.edges:
            u, v = find(u), find(v)
            self.adj[(u, x)] = v
            self.adj[(v, INV[x])] = u

    def read(self, u, word):
        cur = self.find(u)
        for x in word:
            if (cur, x) not in self.adj:
                return None
            cur = self.adj[(cur, x)]
        return cur


def subgroup_graph(gens):
    g = Graph()
    base = g.new()
    for w in gens:
        g.add_path(base, w, base)
    g.fold()
    return g, base


def in_subgroup(gens, w):
    g, base = subgroup_graph(gens)
    return g.read(base, reduce(w)) == g.find(base)


def double_coset_graph(gens, mid):
    """Folded graph of K1 --mid-- K2; w in K mid K iff reduced w reads base1 -> base2."""
    g = Graph()
    b1, b2 = g.new(), g.new()
    for w in gens:
        g.add_path(b1, w, b1)
        g.add_path(b2, w, b2)
    g.add_path(b1, mid, b2)
    g.fold()
    return g, b1, b2


def words(maxlen):
    yield ""
    for L in range(1, maxlen + 1):
        for t in itertools.product("aAcC", repeat=L):
            w = "".join(t)
            if reduce(w) == w:
                yield w
