"""Stallings core sizes of L_j = phi^j(F(a,b)) and L_{j+1} inside L_j.

phi(a) = a, phi(b) = b a b^-2.  Letters: 'a','b' and inverses 'A','B'.
Prints, for each j, the number of vertices of the Stallings core of
L_j = <a, phi^j(b)> in F(a,b), and the free reduced length of phi^j(b).
Also checks the core is a finite cover-free immersion of rank 2
(E - V + 1 == 2).
"""

INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def reduce(w):
    out = []
    for ch in w:
        if out and out[-1] == INV[ch]:
            out.pop()
        else:
            out.append(ch)
    return "".join(out)


def inv(w):
    return "".join(INV[c] for c in reversed(w))


def phi(w):
    img = {"a": "a", "b": "baBB"}
    img["A"] = inv(img["a"])
    img["B"] = inv(img["b"])
    return reduce("".join(img[c] for c in w))


def core(gens):
    # union-find folding on a bouquet of loops
    parent = {}
    edges = set()  # (u, letter in 'ab', v) meaning u --letter--> v
    nxt = [1]

    def new():
        v = nxt[0]
        nxt[0] += 1
        parent[v] = v
        return v

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    parent[0] = 0
    for g in gens:
        cur = 0
        for i, ch in enumerate(g):
            end = 0 if i == len(g) - 1 else new()
            if ch in "ab":
                edges.add((cur, ch, end))
            else:
                edges.add((end, INV[ch], cur))
            cur = end
    changed = True
    while changed:
        changed = False
        es = {(find(u), l, find(v)) for (u, l, v) in edges}
        out, inn = {}, {}
        for (u, l, v) in es:
            if (u, l) in out and out[(u, l)] != v:
                parent[find(out[(u, l)])] = find(v)
                changed = True
                break
            out[(u, l)] = v
            if (v, l) in inn and inn[(v, l)] != u:
                parent[find(inn[(v, l)])] = find(u)
                changed = True
                break
            inn[(v, l)] = u
        edges = es
    es = {(find(u), l, find(v)) for (u, l, v) in edges}
    verts = {u for (u, _, _) in es} | {v for (_, _, v) in es}
    return len(verts), len(es)


if __name__ == "__main__":
    w = "b"
    for j in range(0, 8):
        V, E = core(["a", w])
        print(f"j={j} |phi^j(b)|={len(w)} core_vertices={V} edges={E} rank={E - V + 1}")
        w = phi(w)
