"""Virtual rank-drop census for the fiber formula of relative sandwich cost.

For a finitely generated K <= F_2 = <a,b> and a finite-index subgroup N with
K N = F_2 (K transitive on F_2/N), the free action a_N = s x (F_2 on F_2/N)
satisfies (fiber formula, see the note in research/)

    p_K(a_N) = 1 + (p^N_{K cap N}(s_N) - 1) / d,   d = [F_2 : N],

and p^N_{K cap N}(s_N) <= mrk_N(K cap N), the least rank of a subgroup M'
with K cap N <= M' <= N (group-generated sandwich, fixed price of free
groups).  The group-generated bound in the Bernoulli shift is
p_K(s) <= rmin(K), least rank of an overgroup of K in F_2.

By Miasnikov-Ventura-Weil every overgroup M of H contains an algebraic
extension of H that is a free factor of M; algebraic extensions are
subgroups of folded quotients of the Stallings graph Gamma(H).  So
mrk_N(H) = min rank over vertex partitions of Gamma(H) refining the map
Gamma(H) -> Schreier(N) (these are exactly the quotients whose subgroup
stays inside N), and rmin(K) = min over all vertex partitions of Gamma(K).

A DROP is (K, N) with 1 + (mrk_N(K cap N) - 1)/d < rmin(K).
"""
import itertools, sys

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def reduce(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def fold(nv, edges, base=0):
    """edges: list of (u, lab in 'ab', v). Returns folded (nv, edges, base)."""
    parent = list(range(nv))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    changed = True
    E = list(edges)
    while changed:
        changed = False
        out = {}
        inn = {}
        for (u, l, v) in E:
            u, v = find(u), find(v)
            k = (u, l)
            if k in out and find(out[k]) != v:
                parent[find(out[k])] = v
                changed = True
                break
            out[k] = v
            k2 = (v, l)
            if k2 in inn and find(inn[k2]) != u:
                parent[find(inn[k2])] = u
                changed = True
                break
            inn[k2] = u
    roots = sorted({find(x) for x in range(nv)})
    idx = {r: i for i, r in enumerate(roots)}
    ES = sorted({(idx[find(u)], l, idx[find(v)]) for (u, l, v) in E})
    return len(roots), ES, idx[find(base)]


def stallings(gens):
    nv = 1
    edges = []
    for w in gens:
        w = reduce(w)
        cur = 0
        for i, c in enumerate(w):
            nxt = 0 if i == len(w) - 1 else nv
            if nxt != 0:
                nv += 1
            if c in 'ab':
                edges.append((cur, c, nxt))
            else:
                edges.append((nxt, c.lower(), cur))
            cur = nxt
    return fold(nv, edges)


def rank(nv, edges):
    return len(edges) - nv + 1


def product(K, perms):
    """Component of (base,0) in Gamma(K) x Schreier graph given by perms."""
    nv, E, base = K
    pa, pb = perms
    P = {'a': pa, 'b': pb}
    d = len(pa)
    # BFS over pairs
    start = (base, 0)
    seen = {start: 0}
    order = [start]
    PE = []
    out = {}
    inn = {}
    for (u, l, v) in E:
        out.setdefault(u, []).append((l, v))
        inn.setdefault(v, []).append((l, u))
    i = 0
    while i < len(order):
        (u, c) = order[i]
        i += 1
        for (l, v) in out.get(u, []):
            t = (v, P[l][c])
            if t not in seen:
                seen[t] = len(order)
                order.append(t)
        for (l, w) in inn.get(u, []):
            cinv = P[l].index(c)
            t = (w, cinv)
            if t not in seen:
                seen[t] = len(order)
                order.append(t)
    for (u, l, v) in E:
        for c in range(d):
            if (u, c) in seen and (v, P[l][c]) in seen:
                PE.append((seen[(u, c)], l, seen[(v, P[l][c])]))
    colour = [c for (_, c) in order]
    trans = all((base, c) in seen for c in range(d))
    return len(order), sorted(set(PE)), 0, colour, trans


def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def min_quotient_rank(nv, E, classes, limit=2_000_000):
    """min rank over vertex partitions refining `classes` (list of lists)."""
    best = rank(nv, E)
    count = 0
    witness = None
    for combo in itertools.product(*[list(set_partitions(c)) for c in classes]):
        count += 1
        if count > limit:
            return best, witness, False
        extra = []
        for part in combo:
            for blk in part:
                for x in blk[1:]:
                    extra.append((blk[0], x))
        # merge by union: add identification via folding trick
        parent = list(range(nv))

        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x
        for (x, y) in extra:
            parent[find(y)] = find(x)
        reps = sorted({find(x) for x in range(nv)})
        ri = {r0: i for i, r0 in enumerate(reps)}
        EE = [(ri[find(u)], l, ri[find(v)]) for (u, l, v) in E]
        m, F, _ = fold(len(reps), EE)
        r = rank(m, F)
        if r < best:
            best, witness = r, combo
    return best, witness, True


def covers(d):
    """Transitive pairs of permutations of degree d up to nothing (small d)."""
    perms = list(itertools.permutations(range(d)))
    for pa in perms:
        for pb in perms:
            # transitivity of <pa,pb>
            seen = {0}
            st = [0]
            while st:
                x = st.pop()
                for p in (pa, pb):
                    for y in (p[x], p.index(x)):
                        if y not in seen:
                            seen.add(y)
                            st.append(y)
            if len(seen) == d:
                yield (pa, pb)
