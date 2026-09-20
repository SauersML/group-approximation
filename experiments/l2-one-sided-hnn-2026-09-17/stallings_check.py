"""Stallings folding check for the explicit one-sided input of
research/one-sided-free-hnn-inputs-have-positive-second-l2-betti.md.

F = F(x, y). A = <x^2, y, x y x^-1>, B = <x^2, y^2, x y^2 x^-1>.
Prints, for each subgroup: vertices, edges, rank = E - V + 1, whether the
folded core graph is a covering (finite index) and, if so, the index.
Then prints chi(G) = rk A - rk F for G = F *_{phi : A -> B}.
Capital letters denote inverses.
"""


def fold(words):
    nv = 1
    edges = set()
    for w in words:
        cur = 0
        n = len(w)
        for i, ch in enumerate(w):
            if i == n - 1:
                nxt = 0
            else:
                nxt = nv
                nv += 1
            if ch.islower():
                edges.add((cur, ch, nxt))
            else:
                edges.add((nxt, ch.lower(), cur))
            cur = nxt
    parent = list(range(nv))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    changed = True
    while changed:
        changed = False
        es = {(find(u), l, find(v)) for (u, l, v) in edges}
        out, inc = {}, {}
        for (u, l, v) in sorted(es):
            if (u, l) in out and out[(u, l)] != v:
                parent[find(v)] = find(out[(u, l)])
                changed = True
                break
            out[(u, l)] = v
            if (v, l) in inc and inc[(v, l)] != u:
                parent[find(u)] = find(inc[(v, l)])
                changed = True
                break
            inc[(v, l)] = u
        edges = es
    es = {(find(u), l, find(v)) for (u, l, v) in edges}
    verts = {find(a) for a in range(nv)}
    covering = all(
        any(e[0] == v and e[1] == l for e in es)
        and any(e[2] == v and e[1] == l for e in es)
        for v in verts for l in 'xy')
    return len(verts), len(es), covering


A = ['xx', 'y', 'xyX']
B = ['xx', 'yy', 'xyyX']
rk = {}
for name, gens in (('A', A), ('B', B)):
    V, E, cov = fold(gens)
    rk[name] = E - V + 1
    tag = ('finite index, index ' + str(V)) if cov else 'infinite index'
    print(name, 'V', V, 'E', E, 'rank', E - V + 1, tag)
print('chi(G) = rk A - rk F =', rk['A'] - 2)
print('rk A == rk B:', rk['A'] == rk['B'])
