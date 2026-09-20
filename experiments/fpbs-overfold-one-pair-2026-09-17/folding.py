"""Stallings folding over F(a,b) and the one-pair join criterion.

Letters: 'a','b' and inverses 'A','B'.  A graph is (n, edges) with edges a
list of (u, label, v), label in {'a','b'}, meaning u --label--> v.  Vertex 0
is the base point.

one_pair_joins(G): the set of subgroups <X, g> (g in F) that are NOT arc
extensions is { fold(G / u~w) : u, w in V(G) }  (Lemma 1 of the artifact).
"""
import random

INV = {'a': 'A', 'b': 'B', 'A': 'a', 'B': 'b'}


def reduce_word(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def phi_letter(c):
    # phi(a)=a, phi(b)=b a b^-2
    return {'a': 'a', 'A': 'A', 'b': 'baBB', 'B': 'bbAB'}[c]


def phi(w):
    return reduce_word(''.join(phi_letter(c) for c in w))


def fold(n, edges, pairs=()):
    """Fold graph with extra vertex identifications. Returns (m, edges', root)
    with vertices renumbered 0..m-1 and root[v] the new index of old v."""
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    out = [dict() for _ in range(n)]  # rep -> label -> set of targets (old ids)
    inn = [dict() for _ in range(n)]
    for (u, l, v) in edges:
        out[u].setdefault(l, []).append(v)
        inn[v].setdefault(l, []).append(u)
    stack = list(pairs)
    # initial self-folds
    for v in range(n):
        for d in (out[v], inn[v]):
            for l, ts in d.items():
                for t in ts[1:]:
                    stack.append((ts[0], t))
    while stack:
        x, y = stack.pop()
        x, y = find(x), find(y)
        if x == y:
            continue
        if len(out[x]) + len(inn[x]) < len(out[y]) + len(inn[y]):
            x, y = y, x
        parent[y] = x
        for src, dst in ((out, out), (inn, inn)):
            for l, ts in src[y].items():
                if l in dst[x]:
                    stack.append((dst[x][l][0], ts[0]))
                    dst[x][l].extend(ts)
                else:
                    dst[x][l] = list(ts)
            src[y] = {}
    reps = {}
    root = []
    for v in range(n):
        r = find(v)
        if r not in reps:
            reps[r] = len(reps)
        root.append(reps[r])
    E = set()
    for (u, l, v) in edges:
        E.add((root[u], l, root[v]))
    return len(reps), sorted(E), root


def graph_of(words):
    n = 1
    edges = []
    for w in words:
        w = reduce_word(w)
        if not w:
            continue
        cur = 0
        for i, c in enumerate(w):
            nxt = 0 if i == len(w) - 1 else n
            if i < len(w) - 1:
                n += 1
            if c in 'ab':
                edges.append((cur, c, nxt))
            else:
                edges.append((nxt, c.lower(), cur))
            cur = nxt
    m, E, root = fold(n, edges)
    # base must stay 0
    assert root[0] == 0 or True
    perm = {root[0]: 0}
    k = 1
    for v in range(m):
        if v not in perm:
            perm[v] = k
            k += 1
    E = sorted((perm[u], l, perm[v]) for (u, l, v) in E)
    return m, E


def rank(n, edges):
    # rank of pi_1 of connected graph
    return len(edges) - n + 1


def is_rose(n, edges):
    return n == 1 and len(edges) == 2


def one_pair_to_rose(n, edges, want_all=False):
    """Return list of pairs (u,w) whose identification folds G onto the rose."""
    hits = []
    if is_rose(n, edges):
        return [(0, 0)]
    for u in range(n):
        for w in range(u + 1, n):
            m, E, _ = fold(n, edges, [(u, w)])
            if is_rose(m, E):
                hits.append((u, w))
                if not want_all:
                    return hits
    return hits


def read_path(n, edges, w, start=0):
    """Follow word w from start; return end vertex or None."""
    out = {}
    inn = {}
    for (u, l, v) in edges:
        out[(u, l)] = v
        inn[(v, l)] = u
    cur = start
    for c in w:
        if c in 'ab':
            cur = out.get((cur, c))
        else:
            cur = inn.get((cur, c.lower()))
        if cur is None:
            return None
    return cur


def joins_with(words, g):
    """Stallings graph of <words, g>."""
    return graph_of(list(words) + [g])


def rand_word(L, rng):
    w = ''
    while len(w) < L:
        c = rng.choice('abAB')
        if w and w[-1] == INV[c]:
            continue
        w += c
    return w


def core_based(n, edges):
    """Remove hair not containing base (iteratively prune degree-1 vertices != 0)."""
    alive = set(range(n))
    E = set(edges)
    changed = True
    while changed:
        changed = False
        deg = {v: 0 for v in alive}
        for (u, l, v) in E:
            deg[u] += 1
            deg[v] += 1
        for v in list(alive):
            if v != 0 and deg[v] <= 1:
                alive.discard(v)
                E = {e for e in E if e[0] != v and e[2] != v}
                changed = True
    return alive, E


def canon(n, edges):
    """Canonical form of a folded based graph (after pruning non-base hair)."""
    alive, E = core_based(n, edges)
    out = {}
    for (u, l, v) in E:
        out.setdefault(u, []).append((l, v))
        out.setdefault(v, []).append((l.upper(), u))
    order = {0: 0}
    q = [0]
    i = 0
    while i < len(q):
        v = q[i]
        i += 1
        for (l, t) in sorted(out.get(v, [])):
            if t not in order:
                order[t] = len(order)
                q.append(t)
    return (len(order), tuple(sorted((order[u], l, order[v]) for (u, l, v) in E)))
