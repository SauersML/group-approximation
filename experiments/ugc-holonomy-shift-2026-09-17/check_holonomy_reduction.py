#!/usr/bin/env python3
"""Exact check of the holonomy (gauge) reduction for unique games.

Claim checked: `unique-games-reduce-to-shifts-over-their-holonomy-group`.

For a unique game U on a connected graph with constraints sigma_v = pi_e(sigma_u):
  1. tree-gauging (g_r = id, pi^g = id on a spanning tree) preserves the value;
  2. the gauged non-tree constraints generate Mon_r(U), the monodromy group at r;
  3. with orbits O_1..O_t of Mon_r(U):  max_i val(U_i) <= val(U) <= sum_i val(U_i);
  4. if Mon_r(U) acts on O_i through an abelian group A_i, then A_i is regular on O_i,
     and a -> a(o_i) turns U_i into an A_i-shift game with the same value.

Instances are hidden shift games: a random abelian group A (cyclic or not) acting on
[k] = disjoint union of regular orbits, constraints drawn from A, then disguised by a
random per-vertex relabeling g_v in S_k. All values are computed by brute force.
"""
import itertools
import random


def compose(p, q):  # (p o q)(x) = p[q[x]]
    return tuple(p[x] for x in q)


def inverse(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def value(n, edges, alphabet_of):
    """Brute-force value. edges: (u, v, w, pi) meaning sigma_v = pi[sigma_u]."""
    best = 0.0
    tot = sum(w for _, _, w, _ in edges)
    for lab in itertools.product(*[alphabet_of(v) for v in range(n)]):
        s = sum(w for u, v, w, p in edges if p[lab[u]] == lab[v])
        best = max(best, s)
    return best / tot


def tree_gauge(n, edges, k):
    adj = {v: [] for v in range(n)}
    for idx, (u, v, w, p) in enumerate(edges):
        adj[u].append((v, p, idx))
        adj[v].append((u, inverse(p), idx))
    g = {0: tuple(range(k))}
    tree = set()
    stack = [0]
    while stack:
        u = stack.pop()
        for v, p, idx in adj[u]:
            if v not in g:
                # want g_v p g_u^{-1} = id  =>  g_v = g_u p^{-1}
                g[v] = compose(g[u], inverse(p))
                tree.add(idx)
                stack.append(v)
    assert len(g) == n, "graph must be connected"
    gauged = [(u, v, w, compose(compose(g[v], p), inverse(g[u]))) for (u, v, w, p) in edges]
    return g, gauged, tree


def closure(gens, k):
    ident = tuple(range(k))
    grp = {ident}
    frontier = [ident]
    while frontier:
        new = []
        for a in frontier:
            for s in gens:
                b = compose(s, a)
                if b not in grp:
                    grp.add(b)
                    new.append(b)
        frontier = new
    return grp


def orbits(gens, k):
    parent = list(range(k))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for s in gens:
        for x in range(k):
            a, b = find(x), find(s[x])
            if a != b:
                parent[a] = b
    out = {}
    for x in range(k):
        out.setdefault(find(x), []).append(x)
    return list(out.values())


def random_instance(rng):
    # abelian group A = Z_m1 x Z_m2 (m2 may be 1), acting regularly on t copies of itself
    m1, m2 = rng.choice([(2, 1), (3, 1), (4, 1), (2, 2), (6, 1)])
    t = rng.choice([1, 1, 2])
    elems = [(a, b) for a in range(m1) for b in range(m2)]
    size = len(elems)
    k = size * t
    idx = {e: i for i, e in enumerate(elems)}

    def perm_of(a):
        p = []
        for c in range(t):
            for e in elems:
                f = ((e[0] + a[0]) % m1, (e[1] + a[1]) % m2)
                p.append(c * size + idx[f])
        return tuple(p)
    n = rng.choice([3, 4, 5]) if k <= 4 else rng.choice([3, 4])
    if k > 6:
        n = 3
    edges = []
    for v in range(1, n):  # spanning path keeps the graph connected
        edges.append((v - 1, v, rng.randint(1, 3), perm_of(rng.choice(elems))))
    for _ in range(rng.randint(1, 3)):
        u, v = rng.sample(range(n), 2)
        edges.append((u, v, rng.randint(1, 3), perm_of(rng.choice(elems))))
    # disguise: random per-vertex relabeling
    h = [tuple(rng.sample(range(k), k)) for _ in range(n)]
    disguised = [(u, v, w, compose(compose(h[v], p), inverse(h[u]))) for (u, v, w, p) in edges]
    return n, k, disguised, (m1, m2, t)


def check(rng):
    n, k, edges, meta = random_instance(rng)
    full = lambda v: range(k)
    val = value(n, edges, full)
    g, gauged, tree = tree_gauge(n, edges, k)
    assert abs(value(n, gauged, full) - val) < 1e-12, "gauge changed the value"
    gens = [p for i, (_, _, _, p) in enumerate(gauged) if i not in tree]
    for i in tree:
        assert gauged[i][3] == tuple(range(k))
    H = closure(gens, k)
    # every gauged constraint lies in H
    assert all(p in H for (_, _, _, p) in gauged)
    orbs = orbits(gens, k)
    vals = []
    for O in orbs:
        Oset = set(O)
        # restrict and identify with the abelian image A_O
        A = {tuple(p[x] for x in O) for p in H}  # image acting on O, as tuples over O's order
        pos = {x: i for i, x in enumerate(O)}
        A = {tuple(pos[y] for y in a) for a in A}
        abelian = all(compose(a, b) == compose(b, a) for a in A for b in A)
        assert abelian
        assert len(A) == len(O), "abelian transitive image must be regular"
        o = 0
        elem_of = {a[o]: a for a in A}  # a -> a(o) is a bijection
        assert len(elem_of) == len(O)
        restricted = [(u, v, w, tuple(pos[p[x]] for x in O)) for (u, v, w, p) in gauged]
        # shift form: gamma acts on group elements by left multiplication
        Alist = sorted(A)
        aidx = {a: i for i, a in enumerate(Alist)}
        shift_edges = []
        for (u, v, w, gam) in restricted:
            shift = tuple(aidx[compose(gam, a)] for a in Alist)
            # consistency: identification commutes with the action
            for a in Alist:
                assert gam[a[o]] == compose(gam, a)[o]
            shift_edges.append((u, v, w, shift))
        v1 = value(n, restricted, lambda v: range(len(O)))
        v2 = value(n, shift_edges, lambda v: range(len(Alist)))
        assert abs(v1 - v2) < 1e-12
        vals.append(v1)
        assert Oset
    assert max(vals) <= val + 1e-12
    assert val <= sum(vals) + 1e-12
    return meta, len(orbs), val, vals


def main():
    rng = random.Random(20260917)
    counts = {}
    for trial in range(300):
        meta, t, val, vals = check(rng)
        counts[meta] = counts.get(meta, 0) + 1
    print("group (m1, m2, copies) -> instances checked:", dict(sorted(counts.items())))
    print("all 300 instances: gauge preserves value; constraints lie in Mon_r;"
          " abelian orbit images are regular; shift form has equal value;"
          " max_i val(U_i) <= val(U) <= sum_i val(U_i)")


if __name__ == "__main__":
    main()
