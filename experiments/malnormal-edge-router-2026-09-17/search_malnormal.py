#!/usr/bin/env python3
"""Search for a rank-4 MALNORMAL subgroup C2 = <a, y1, y2, y3> of F(a,b) such that

    G0 = < t, b | t^k = y_k(t^N, b), k = 1,2,3 >   (N = 4)

is trivial and b notin C2.

Use: second amalgam Q2 = (Q1 * <t>) *_{C1=C2} F(a,b),  C1 = <t^4, r_k t^k>,
t^4 <-> a, r_k t^k <-> y_k, with r_1, r_2, r_3 pairwise distinct nontrivial
elements generating Q1.  Malnormality of the edge group in one vertex group
gives acylindricity of the Bass--Serre action internally (no Minasyan--Osin).

Words are strings over 'aAbB' ('A' = a^-1, 'B' = b^-1); for G0 we use 'tTbB'.

Checks:
  * Stallings graph of C2 folded, rank 4, no b-loop at base (b notin C2);
  * malnormality via the Kapovich--Myasnikov pullback criterion (every
    off-diagonal component of Gamma x Gamma is a tree), cross-checked by
    brute force over short conjugators;
  * abelianisation of G0 trivial;
  * coset enumeration of G0 over <b> has index 1 (so G0 cyclic, hence trivial).
"""
import itertools, sys
from collections import deque

INV = {c: c.swapcase() for c in "aAbBtT"}

def inv(w):
    return "".join(INV[c] for c in reversed(w))

def reduce_word(w):
    st = []
    for c in w:
        if st and st[-1] == INV[c]:
            st.pop()
        else:
            st.append(c)
    return "".join(st)

# ---------------- Stallings folding ----------------
def stallings(gens):
    parent = {0: 0}
    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    edges = set()
    nv = 1
    for w in gens:
        cur = 0
        for i, c in enumerate(w):
            if i == len(w) - 1:
                nxt = 0
            else:
                nxt = nv; parent[nxt] = nxt; nv += 1
            edges.add((cur, c, nxt)); edges.add((nxt, INV[c], cur))
            cur = nxt
    changed = True
    while changed:
        changed = False
        out = {}
        for (u, c, v) in list(edges):
            u2, v2 = find(u), find(v)
            key = (u2, c)
            if key in out and find(out[key]) != v2:
                parent[find(out[key])] = v2
                changed = True
            else:
                out[key] = v2
        edges = {(find(u), c, find(v)) for (u, c, v) in edges}
    verts = {find(v) for v in parent}
    base = find(0)
    out = {}
    for (u, c, v) in edges:
        assert (u, c) not in out or out[(u, c)] == v
        out[(u, c)] = v
    # prune hanging trees (keep base)
    deg = {v: 0 for v in verts}
    for (u, c, v) in edges:
        deg[u] += 1
    alive = set(verts)
    q = deque(v for v in verts if deg[v] == 1 and v != base)
    while q:
        v = q.popleft()
        if v not in alive:
            continue
        alive.discard(v)
        for c in "aAbB":
            if (v, c) in out and out[(v, c)] in alive:
                w = out[(v, c)]
                deg[w] -= 1
                if deg[w] == 1 and w != base:
                    q.append(w)
    out = {k: v for k, v in out.items() if k[0] in alive and v in alive}
    return base, alive, out

def rank(G):
    base, V, out = G
    return len(out) // 2 - len(V) + 1

def component_ranks(G1, G2, start=None):
    """ranks of components of the pullback G1 x G2; returns list of (vertices, rank)."""
    b1, V1, o1 = G1; b2, V2, o2 = G2
    seen = set(); comps = []
    starts = [start] if start else [(p, q) for p in V1 for q in V2]
    for s in starts:
        if s in seen:
            continue
        seen.add(s); stack = [s]; verts = [s]; ec = 0
        while stack:
            (p, q) = stack.pop()
            for c in "aAbB":
                if (p, c) in o1 and (q, c) in o2:
                    ec += 1
                    n = (o1[(p, c)], o2[(q, c)])
                    if n not in seen:
                        seen.add(n); stack.append(n); verts.append(n)
        comps.append((verts, ec // 2 - len(verts) + 1))
    return comps

def is_malnormal(G):
    for verts, r in component_ranks(G, G):
        diag = any(p == q for (p, q) in verts)
        if diag:
            assert all(p == q for (p, q) in verts)
        elif r > 0:
            return False
    return True

def in_subgroup(G, w):
    base, V, out = G
    v = base
    for c in w:
        if (v, c) not in out:
            return False
        v = out[(v, c)]
    return v == base

def brute_malnormal(gens, G, L=4):
    for n in range(1, L + 1):
        for g in itertools.product("aAbB", repeat=n):
            g = "".join(g)
            if reduce_word(g) != g or in_subgroup(G, g):
                continue
            H = stallings([reduce_word(g + w + inv(g)) for w in gens])
            (verts, r), = component_ranks(G, H, start=(G[0], H[0]))
            if r > 0:
                return False, g
    return True, None

# ---------------- coset enumeration (HLT with coincidences) ----------------
def coset_index(gens, rels, subgens, limit=200000):
    """Index of <subgens> in <gens | rels>. gens: lowercase letters; inverse = uppercase."""
    letters = []
    for g in gens:
        letters += [g, g.upper()]
    table = [dict()]
    live = [True]
    parent = [0]
    def find(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c
    def define(c, x):
        n = len(table)
        if n >= limit:
            raise OverflowError
        table.append(dict()); live.append(True); parent.append(n)
        table[c][x] = n; table[n][INV[x]] = c
        return n
    def coincidence(c1, c2):
        queue = [(c1, c2)]
        while queue:
            a, b = queue.pop()
            a, b = find(a), find(b)
            if a == b:
                continue
            if a > b:
                a, b = b, a
            parent[b] = a; live[b] = False
            for x, d in list(table[b].items()):
                d = find(d)
                # remove inverse entry at d
                if table[d].get(INV[x]) is not None and find(table[d][INV[x]]) == b:
                    del table[d][INV[x]]
                if x in table[a]:
                    queue.append((table[a][x], d))
                else:
                    table[a][x] = d
                    if INV[x] in table[d]:
                        queue.append((table[d][INV[x]], a))
                    else:
                        table[d][INV[x]] = a
            table[b] = {}
    def scan_fill(c, w):
        # scan word w from coset c, defining as needed; then close
        while True:
            c = find(c)
            f = c; i = 0; j = len(w) - 1; b = c
            while i <= j and w[i] in table[find(f)]:
                f = find(table[find(f)][w[i]]); i += 1
            if i > j:
                if find(f) != find(c):
                    coincidence(f, c)
                return
            while j >= i and INV[w[j]] in table[find(b)]:
                b = find(table[find(b)][INV[w[j]]]); j -= 1
            if j < i:
                coincidence(f, b); return
            if i == j:
                f = find(f); b = find(b)
                if w[i] in table[f]:
                    coincidence(table[f][w[i]], b)
                elif INV[w[i]] in table[b]:
                    coincidence(table[b][INV[w[i]]], f)
                else:
                    table[f][w[i]] = b; table[b][INV[w[i]]] = f
                return
            define(find(f), w[i])
    for h in subgens:
        scan_fill(0, h)
    c = 0
    while c < len(table):
        if live[c] and find(c) == c:
            for r in rels:
                for k in range(len(r)):
                    if not live[find(c)]:
                        break
                    scan_fill(c, r[k:] + r[:k])
            if live[c] and find(c) == c:
                for x in letters:
                    if find(c) == c and x not in table[c]:
                        define(c, x)
        c += 1
    return sum(1 for i in range(len(table)) if live[i] and find(i) == i)

# ---------------- G0 ----------------
N = 4

def g0_relators(ys):
    rels = []
    for k, y in enumerate(ys, start=1):
        sub = y.replace("a", "t" * N).replace("A", "T" * N)
        rels.append(reduce_word("T" * k + sub))
    return rels

def abel_trivial(ys):
    rows = []
    for k, y in enumerate(ys, start=1):
        al = y.count("a") - y.count("A"); be = y.count("b") - y.count("B")
        rows.append((k - N * al, -be))
    from math import gcd
    g = 0
    for i in range(3):
        for j in range(i + 1, 3):
            g = gcd(g, abs(rows[i][0] * rows[j][1] - rows[i][1] * rows[j][0]))
    return g == 1

def words(L):
    res = []
    for n in range(1, L + 1):
        for w in itertools.product("aAbB", repeat=n):
            w = "".join(w)
            if reduce_word(w) == w and ("b" in w or "B" in w):
                res.append(w)
    return res

def search(L, maxfound=20):
    W = words(L)
    found = []
    base_ok = {}
    for y1, y2 in itertools.combinations(W, 2):
        G = stallings(["a", y1, y2])
        if rank(G) != 3 or in_subgroup(G, "b") or not is_malnormal(G):
            continue
        for y3 in W:
            if y3 <= y2:
                continue
            gens = ["a", y1, y2, y3]
            G = stallings(gens)
            if rank(G) != 4 or in_subgroup(G, "b") or not is_malnormal(G):
                continue
            for perm in itertools.permutations([y1, y2, y3]):
                if not abel_trivial(perm):
                    continue
                try:
                    idx = coset_index("tb", g0_relators(perm), ["b"], limit=20000)
                except OverflowError:
                    continue
                if idx == 1 and coset_index("tb", g0_relators(perm), [], limit=50000) == 1:
                    found.append(perm)
                    print("FOUND", perm, "relators", g0_relators(perm), flush=True)
                    if len(found) >= maxfound:
                        return found
    return found

CHOSEN = ("baabb", "babAb", "bbbaB")   # y1 = b a^2 b^2, y2 = b a b a^-1 b, y3 = b^3 a b^-1

def sanity():
    # coset enumerator on groups of known order
    assert coset_index("tb", ["tt", "bb", "tbTB"], []) == 4            # Z2 x Z2
    assert coset_index("tb", ["ttt", "bb", "tbtb"], []) == 6           # S3
    assert coset_index("tb", ["tttt", "bbb", "tbtb"], []) == 24        # (2,3,4) = S4
    assert coset_index("tb", ["tt", "bbb", "tbtbtbtbtb"], []) == 60    # A5
    assert coset_index("tb", ["tt", "bbb", "tbtbtbtbtb"], ["b"]) == 20
    assert coset_index("tb", ["tt", "bbb", "tbtbtbtbtbtbtb", "tbTBtbTBtbTBtbTB"], []) == 168
    assert coset_index("tb", ["b" * 31, "tbTBBBBB", "t" * 18], []) == 558  # Z31 x| Z18
    assert coset_index("tb", ["tbTBB", "btBTT"], []) == 1              # trivial, needs coincidences
    # malnormality checker
    assert is_malnormal(stallings(["a"]))
    assert not is_malnormal(stallings(["aa"]))
    assert not is_malnormal(stallings(["a", "Bab"]))
    print("sanity checks passed")

def verify(ys=CHOSEN):
    gens = ["a"] + list(ys)
    G = stallings(gens)
    base, V, out = G
    print("C2 =", gens)
    print("  Stallings graph: |V| =", len(V), " rank =", rank(G))
    for (u, c), v in sorted(out.items()):
        if c.islower():
            print(f"    {u} -{c}-> {v}")
    assert rank(G) == 4, "the four words are not a free basis"
    assert not in_subgroup(G, "b"), "b in C2"
    assert is_malnormal(G), "C2 not malnormal (pullback criterion)"
    ok, g = brute_malnormal(gens, G, L=6)
    assert ok, ("brute force found a conjugator", g)
    print("  rank 4 (basis), b notin C2, malnormal: pullback criterion + brute force over conjugators of length <= 6")
    rels = g0_relators(ys)
    print("  G0 relators t^-k y_k(t^4,b):", rels)
    assert abel_trivial(ys)
    assert coset_index("tb", rels, [], limit=200000) == 1
    assert coset_index("tb", rels, ["b"], limit=200000) == 1
    assert coset_index("tb", rels, ["t"], limit=200000) == 1
    print("  G0 abelianisation trivial; HLT coset enumeration: |G0| = 1")
    try:
        from sympy.combinatorics.free_groups import free_group
        from sympy.combinatorics.fp_groups import FpGroup, coset_enumeration_r
        F, t, b = free_group("t b")
        d = {"t": t, "T": t ** -1, "b": b, "B": b ** -1}
        def tow(w):
            x = F.identity
            for c in w:
                x = x * d[c]
            return x
        C = coset_enumeration_r(FpGroup(F, [tow(r) for r in rels]), [], max_cosets=200000)
        C.compress()
        assert len(C.table) == 1
        print("  sympy coset_enumeration_r cross-check: |G0| = 1")
    except ImportError:
        print("  (sympy not installed; independent cross-check skipped)")
    print("VERIFIED")

if __name__ == "__main__":
    sanity()
    if len(sys.argv) > 1 and sys.argv[1] == "search":
        L = int(sys.argv[2]) if len(sys.argv) > 2 else 5
        search(L)
    else:
        verify()
