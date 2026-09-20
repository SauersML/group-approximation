"""Minimal Stallings-graph library over F(a,b); letters a,A,b,B (A=a^-1).

Words are strings.  A folded graph is (adj, base) with adj[v][x] = w.
"""
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def red(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return ''.join(out)


def inv(w):
    return ''.join(INV[x] for x in reversed(w))


def fold_graph(words):
    """Folded Stallings graph of <words>, base 0."""
    edges = []
    n = 1
    for w in words:
        w = red(w)
        if not w:
            continue
        cur = 0
        for i, x in enumerate(w):
            nxt = 0 if i == len(w) - 1 else n
            if i < len(w) - 1:
                n += 1
            edges.append((cur, x, nxt))
            cur = nxt
    parent = list(range(n))

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    changed = True
    while changed:
        changed = False
        adj = {}
        for (u, x, v) in edges:
            u, v = find(u), find(v)
            for (p, y, q) in ((u, x, v), (v, INV[x], u)):
                d = adj.setdefault(p, {})
                if y in d and find(d[y]) != q:
                    r1, r2 = find(d[y]), q
                    parent[max(r1, r2)] = min(r1, r2)
                    changed = True
                else:
                    d[y] = q
    adj = {}
    for (u, x, v) in edges:
        u, v = find(u), find(v)
        adj.setdefault(u, {})[x] = v
        adj.setdefault(v, {})[INV[x]] = u
    base = find(0)
    adj.setdefault(base, {})
    # relabel
    idx = {base: 0}
    for v in adj:
        if v not in idx:
            idx[v] = len(idx)
    return {idx[v]: {x: idx[w] for x, w in d.items()} for v, d in adj.items()}, 0


def member(G, w):
    adj, v = G
    for x in red(w):
        if x not in adj[v]:
            return False
        v = adj[v][x]
    return v == 0


def rank(G):
    adj, _ = G
    e = sum(len(d) for d in adj.values()) // 2
    return e - len(adj) + 1


def basis(G):
    """Return (tree_paths, gens, edge_index): gens as words; edge_index maps
    a positive non-tree edge (u,x) to generator index."""
    adj, base = G
    path = {base: ''}
    order = [base]
    tree = set()
    for v in order:
        for x, w in sorted(adj[v].items()):
            if w not in path:
                path[w] = path[v] + x
                order.append(w)
                tree.add((v, x))
                tree.add((w, INV[x]))
    gens, eidx = [], {}
    for v in adj:
        for x, w in adj[v].items():
            if x in 'ab' and (v, x) not in tree:
                eidx[(v, x)] = len(gens)
                gens.append(red(path[v] + x + inv(path[w])))
    return path, gens, eidx


def coords(G, B, w):
    """Express w (in <G>) as a list of (gen index, +-1) using basis B."""
    adj, v = G
    _, _, eidx = B
    out = []
    for x in red(w):
        w2 = adj[v][x]
        if x in 'ab' and (v, x) in eidx:
            out.append((eidx[(v, x)], 1))
        elif x in 'AB' and (w2, INV[x]) in eidx:
            out.append((eidx[(w2, INV[x])], -1))
        v = w2
    assert v == 0
    return out


def intersect(G1, G2):
    """Folded graph of <G1> cap <G2> (base component of the product)."""
    a1, _ = G1
    a2, _ = G2
    idx = {(0, 0): 0}
    order = [(0, 0)]
    adj = {0: {}}
    for (p, q) in order:
        i = idx[(p, q)]
        for x, p2 in a1[p].items():
            if x in a2[q]:
                t = (p2, a2[q][x])
                if t not in idx:
                    idx[t] = len(idx)
                    order.append(t)
                    adj[idx[t]] = {}
                adj[i][x] = idx[t]
    return prune((adj, 0))


def prune(G):
    adj, base = G
    adj = {v: dict(d) for v, d in adj.items()}
    changed = True
    while changed:
        changed = False
        for v in list(adj):
            if v != base and len(adj[v]) == 1:
                (x, w), = adj[v].items()
                del adj[w][INV[x]]
                del adj[v]
                changed = True
    idx = {base: 0}
    for v in adj:
        if v not in idx:
            idx[v] = len(idx)
    return {idx[v]: {x: idx[w] for x, w in d.items()} for v, d in adj.items()}, 0


def phi(w):
    """phi: a -> a, b -> b a b^-2."""
    img = {'a': 'a', 'A': 'A', 'b': 'baBB', 'B': 'bbAB'}
    return red(''.join(img[x] for x in w))


def L(j):
    gens = ['a', 'b']
    for _ in range(j):
        gens = [phi(g) for g in gens]
    return gens
