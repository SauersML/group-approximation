"""Stallings graphs over F(c,d) and contact subgroups.

Letters: 'c','d' and inverses 'C','D'. A Stallings graph is a dict
out[v][letter] = w for positive letters, with inverse table.

Functions:
  fold(words)            -> (graph, base) core Stallings graph of <words>
  intersect_conj(G,b,g)  -> rank of H cap g H g^-1 (via product graph)
  finite_index(G)        -> True iff graph is a covering (every vertex has all 4 half-edges)
"""
from collections import defaultdict

INV = {'c': 'C', 'C': 'c', 'd': 'D', 'D': 'd'}
POS = ['c', 'd']


class Graph:
    def __init__(self):
        self.adj = defaultdict(dict)  # adj[v][letter] = w (all four letters)
        self.n = 0

    def new(self):
        v = self.n
        self.n += 1
        self.adj[v]
        return v

    def add(self, u, l, w):
        self.adj[u][l] = w
        self.adj[w][INV[l]] = u


def fold(words):
    """Build the Stallings graph of <words> by naive folding."""
    edges = []  # (u, letter, w) positive or negative letters
    n = 1
    for wd in words:
        cur = 0
        for i, l in enumerate(wd):
            nxt = 0 if i == len(wd) - 1 else n
            if i < len(wd) - 1:
                n += 1
            edges.append((cur, l, nxt))
            cur = nxt
    # union-find folding
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    changed = True
    while changed:
        changed = False
        out = {}
        for (u, l, w) in edges:
            for (a, lab, b) in ((u, l, w), (w, INV[l], u)):
                a, b = find(a), find(b)
                key = (a, lab)
                if key in out:
                    b2 = find(out[key])
                    if b2 != b:
                        parent[b2] = b
                        changed = True
                else:
                    out[key] = b
    G = Graph()
    ids = {}
    for x in range(n):
        r = find(x)
        if r not in ids:
            ids[r] = G.new()
    for (u, l, w) in edges:
        G.add(ids[find(u)], l, ids[find(w)])
    return G, ids[find(0)]


def prune(G, base):
    """Remove degree-one vertices other than base (core graph)."""
    alive = set(range(G.n))
    ch = True
    while ch:
        ch = False
        for v in list(alive):
            if v == base:
                continue
            nb = [w for w in G.adj[v].values() if w in alive]
            if len(nb) <= 1 and not (len(nb) == 1 and nb[0] == v):
                if len([l for l, w in G.adj[v].items() if w in alive]) <= 1:
                    alive.discard(v)
                    ch = True
    return alive


def read(G, v, word):
    for l in word:
        if l not in G.adj[v]:
            return None
        v = G.adj[v][l]
    return v


def is_covering(G):
    return all(len(G.adj[v]) == 4 for v in range(G.n))


def rank_component(G1, G2, start):
    """Rank of pi_1 of the component of the product graph containing start."""
    seen = {start}
    stack = [start]
    E = 0
    while stack:
        (p, q) = stack.pop()
        for l in POS:
            if l in G1.adj[p] and l in G2.adj[q]:
                E += 1
                nx = (G1.adj[p][l], G2.adj[q][l])
                if nx not in seen:
                    seen.add(nx)
                    stack.append(nx)
        for l in ['C', 'D']:
            if l in G1.adj[p] and l in G2.adj[q]:
                nx = (G1.adj[p][l], G2.adj[q][l])
                if nx not in seen:
                    seen.add(nx)
                    stack.append(nx)
    return E - len(seen) + 1


def conj_intersection_rank(G, base, g):
    """rank of H cap g^-1 H g, where H = pi_1(G, base).

    x in H and g x g^-1 in H  <=>  x is a loop at base and a loop at base.g^-1... we
    use: g^-1 H g = pi_1(G, base . g) if g readable; in general fold H with g.
    """
    # H^g := g^-1 H g has Stallings graph obtained by attaching path g at base.
    # Build directly: loops at base in G read by x, and g x g^-1 loop at base <=>
    # x is a loop at vertex reached by reading g (possibly off the graph).
    return None


def subgroup_rank_intersection(words1, words2):
    G1, b1 = fold(words1)
    G2, b2 = fold(words2)
    return rank_component(G1, G2, (b1, b2))


def inv(w):
    return ''.join(INV[l] for l in reversed(w))


def core(G, base):
    """Vertices of the core (repeatedly delete degree-1 vertices except base)."""
    alive = set(range(G.n))
    ch = True
    while ch:
        ch = False
        for v in list(alive):
            if v == base:
                continue
            deg = sum(1 for l, w in G.adj[v].items() if w in alive)
            if deg <= 1:
                alive.discard(v)
                ch = True
    return alive


def malnormal(words):
    """H malnormal iff every product-graph component through an off-diagonal
    vertex (p,q), p != q, of core(G) x core(G) is a tree.  Returns
    (is_malnormal, witness vertex or None)."""
    G, b = fold(words)
    A = core(G, b)
    done = set()
    for p in A:
        for q in A:
            if p == q or (p, q) in done:
                continue
            # explore component within core vertices
            seen = {(p, q)}
            stack = [(p, q)]
            E = 0
            while stack:
                (x, y) = stack.pop()
                for l in ['c', 'd', 'C', 'D']:
                    if l in G.adj[x] and l in G.adj[y]:
                        nx = (G.adj[x][l], G.adj[y][l])
                        if nx[0] in A and nx[1] in A:
                            if l in POS:
                                E += 1
                            if nx not in seen:
                                seen.add(nx)
                                stack.append(nx)
            done |= seen
            has_diag = any(x == y for (x, y) in seen)
            if not has_diag and E - len(seen) + 1 > 0:
                return False, (p, q)
    return True, None


if __name__ == '__main__':
    import sys
    v = 'cdcDcd'
    for H in (['c', v], ['d', v]):
        for g in ['c', 'C', 'd', 'D']:
            conj = [g + h + inv(g) for h in H]
            r = subgroup_rank_intersection(H, conj)
            G, b = fold(H)
            print('H=<%s>' % ','.join(H), 'g=', g, 'rank(H cap gHg^-1)=', r,
                  'stallings size', G.n, 'covering', is_covering(G))
