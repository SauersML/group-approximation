#!/usr/bin/env python3
"""Find a rank-2 malnormal subgroup F = <u, v> of the free group F(x, y) such that no nontrivial
power of x is conjugate into F.  Certificates are Stallings graphs:

* F is malnormal in F(x,y) iff every component of the fibre product Gamma_F x Gamma_F that
  contains no diagonal vertex (p, p) is a tree (Kapovich--Myasnikov, "Stallings foldings and
  subgroups of free groups", J. Algebra 248 (2002), Prop. 9.10).
* x^n (n != 0) is conjugate into F iff the core graph Gamma_F has a closed x-labelled loop,
  i.e. the partial permutation of vertices given by the x-edges has a cycle.
* rank(F) = E - V + 1 of the (core, base-point) graph; the words u, v are then a free basis.

Output: the first certificate found among short words, and the check that the Stallings graph
is a core graph with the given rank.
"""
import itertools

LET = "xXyY"
INV = {"x": "X", "X": "x", "y": "Y", "Y": "y"}


def reduce(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return "".join(out)


def stallings(words):
    # edges: dict (vertex, letter) -> vertex for positive letters x, y; inverse maps kept too
    fwd = {}  # (v, 'x'|'y') -> w
    bwd = {}  # (w, 'x'|'y') -> v
    parent = {}
    nv = [1]

    def new():
        v = nv[0]; nv[0] += 1; parent[v] = v; return v

    parent[0] = 0

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    edges = []
    for w in words:
        cur = 0
        for i, c in enumerate(w):
            nxt = 0 if i == len(w) - 1 else new()
            if c in "xy":
                edges.append((cur, c, nxt))
            else:
                edges.append((nxt, c.lower(), cur))
            cur = nxt
    # fold
    changed = True
    while changed:
        changed = False
        es = {(find(a), l, find(b)) for a, l, b in edges}
        edges = list(es)
        seen_f, seen_b = {}, {}
        for a, l, b in edges:
            if (a, l) in seen_f and seen_f[(a, l)] != b:
                parent[find(b)] = find(seen_f[(a, l)]); changed = True; break
            seen_f[(a, l)] = b
            if (b, l) in seen_b and seen_b[(b, l)] != a:
                parent[find(a)] = find(seen_b[(b, l)]); changed = True; break
            seen_b[(b, l)] = a
    edges = list({(find(a), l, find(b)) for a, l, b in edges})
    verts = {find(0)} | {a for a, _, _ in edges} | {b for _, _, b in edges}
    return find(0), verts, edges


def is_core(base, verts, edges):
    deg = {v: 0 for v in verts}
    for a, _, b in edges:
        deg[a] += 1; deg[b] += 1
    return all(d >= 2 for v, d in deg.items() if v != base)


def components(nodes, adj):
    seen, comps = set(), []
    for s in nodes:
        if s in seen:
            continue
        stack, comp = [s], []
        seen.add(s)
        while stack:
            v = stack.pop(); comp.append(v)
            for w in adj.get(v, ()):
                if w not in seen:
                    seen.add(w); stack.append(w)
        comps.append(comp)
    return comps


def malnormal(verts, edges):
    pe = []
    for a, l, b in edges:
        for c, l2, d in edges:
            if l == l2:
                pe.append(((a, c), (b, d)))
    nodes = {(p, q) for p in verts for q in verts}
    adj = {}
    for u, w in pe:
        adj.setdefault(u, []).append(w); adj.setdefault(w, []).append(u)
    for comp in components(nodes, adj):
        cs = set(comp)
        if any(p == q for p, q in comp):
            continue
        ne = sum(1 for u, w in pe if u in cs)
        if ne >= len(comp):  # a connected graph with E >= V has a cycle
            return False
    return True


def x_cycle(verts, edges):
    f = {a: b for a, l, b in edges if l == "x"}
    for s in f:
        v, steps = s, 0
        while v in f and steps <= len(verts):
            v = f[v]; steps += 1
            if v == s:
                return True
    return False


def words(n):
    for L in range(1, n + 1):
        for t in itertools.product(LET, repeat=L):
            w = "".join(t)
            if reduce(w) == w:
                yield w


def main():
    tested = 0
    for u in words(5):
        for v in words(5):
            if v <= u:
                continue
            base, verts, edges = stallings([u, v])
            tested += 1
            rank = len(edges) - len(verts) + 1
            if rank != 2 or not is_core(base, verts, edges):
                continue
            if x_cycle(verts, edges) or not malnormal(verts, edges):
                continue
            print(f"pairs tested before success: {tested}")
            print(f"F = <u, v>, u = {u}, v = {v}")
            print(f"Stallings core graph: {len(verts)} vertices, {len(edges)} edges, rank {rank}, base core: True")
            print("malnormal (every non-diagonal fibre-product component is a tree): True")
            print("no x-labelled cycle (no power of x conjugate into F): True")
            # sanity: known non-malnormal examples are rejected
            for bad in (["x", "yxY"], ["xx", "yy"], ["x", "yy"]):
                b, vs, es = stallings(bad)
                print(f"control <{', '.join(bad)}>: malnormal = {malnormal(vs, es)}")
            return
    print("no example found")


if __name__ == "__main__":
    main()
