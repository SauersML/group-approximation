"""Noncrossing partition lattice NCP_n, apartments (noncrossing spanning trees), opposite universal pairs.

Points are 0..n-1 on a circle. A partition is a tuple lab with lab[i] = min element of the block of i.
"""
from itertools import combinations
from functools import lru_cache


def set_partitions(n):
    def rec(i, lab, mins):
        if i == n:
            yield tuple(lab)
            return
        for m in mins:
            lab.append(m)
            yield from rec(i + 1, lab, mins)
            lab.pop()
        lab.append(i)
        mins.append(i)
        yield from rec(i + 1, lab, mins)
        mins.pop()
        lab.pop()
    yield from rec(0, [], [])


def blocks(p):
    d = {}
    for i, m in enumerate(p):
        d.setdefault(m, []).append(i)
    return [tuple(b) for b in d.values()]


def crossing_sets(A, B):
    """A, B disjoint subsets of 0..n-1: do they cross (a<b<c<d, a,c in A, b,d in B or vice versa)?"""
    tagged = sorted([(x, 0) for x in A] + [(x, 1) for x in B])
    seq = [t for _, t in tagged]
    # compress runs
    comp = [seq[0]]
    for t in seq[1:]:
        if t != comp[-1]:
            comp.append(t)
    if len(comp) > 1 and comp[0] == comp[-1]:
        comp.pop()
    return len(comp) >= 4


def is_noncrossing(p):
    bs = [b for b in blocks(p) if len(b) > 1]
    for A, B in combinations(bs, 2):
        if crossing_sets(A, B):
            return False
    return True


def canon(groups, n):
    lab = [None] * n
    for g in groups:
        m = min(g)
        for x in g:
            lab[x] = m
    return tuple(lab)


def leq(p, q):
    """p refines q"""
    return all(q[i] == q[p[i]] for i in range(len(p)))


def nblocks(p):
    return len(set(p))


def rank(p):
    return len(p) - nblocks(p)


def join_P(p, q):
    n = len(p)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i in range(n):
        for r in (p[i], q[i]):
            a, b = find(i), find(r)
            if a != b:
                parent[max(a, b)] = min(a, b)
    groups = {}
    for i in range(n):
        groups.setdefault(find(i), []).append(i)
    return canon(groups.values(), n)


def meet(p, q):
    n = len(p)
    d = {}
    for i in range(n):
        d.setdefault((p[i], q[i]), []).append(i)
    return canon(d.values(), n)


def kreweras(p):
    """Kreweras complement: primed point k' sits between k and k+1 (mod n). k'~l' (k<l) iff every block of p
    lies inside {k+1..l} or is disjoint from it."""
    n = len(p)
    bs = blocks(p)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for k in range(n):
        for l in range(k + 1, n):
            S = set(range(k + 1, l + 1))
            if all(set(b) <= S or not (set(b) & S) for b in bs):
                a, c = find(k), find(l)
                if a != c:
                    parent[max(a, c)] = min(a, c)
    groups = {}
    for i in range(n):
        groups.setdefault(find(i), []).append(i)
    return canon(groups.values(), n)


def cyclic_interval(s, k, n):
    return tuple(sorted((s + t) % n for t in range(k)))


def universal(p):
    bs = [b for b in blocks(p) if len(b) > 1]
    if len(bs) != 1:
        return False
    B = set(bs[0])
    n = len(p)
    k = len(B)
    return any(set(cyclic_interval(s, k, n)) == B for s in range(n))


def partition_from_block(B, n):
    return canon([B] + [(i,) for i in range(n) if i not in B], n)


def opposite_universal_pairs(n):
    """Unordered pairs {v, w} of universal partitions whose blocks are cyclic intervals I, J with
    |I| + |J| = n + 1, |I|,|J| >= 2, I u J = all, |I n J| = 1."""
    ivs = set()
    for k in range(2, n):
        for s in range(n):
            ivs.add(cyclic_interval(s, k, n))
    pairs = set()
    for I in ivs:
        for J in ivs:
            if len(I) + len(J) == n + 1 and len(set(I) & set(J)) == 1 and set(I) | set(J) == set(range(n)):
                v, w = partition_from_block(I, n), partition_from_block(J, n)
                pairs.add(tuple(sorted((v, w))))
    return sorted(pairs)


def noncrossing_trees(n):
    """All noncrossing spanning trees on n points in convex position (edge lists)."""
    edges = list(combinations(range(n), 2))

    def cross(e, f):
        a, b = e
        c, d = f
        if len({a, b, c, d}) < 4:
            return False
        return (a < c < b < d) or (c < a < d < b)
    res = []

    def rec(idx, chosen, parent):
        if len(chosen) == n - 1:
            res.append(tuple(chosen))
            return
        if idx == len(edges):
            return
        if len(edges) - idx < n - 1 - len(chosen):
            return
        e = edges[idx]
        # include
        if all(not cross(e, f) for f in chosen):
            p2 = list(parent)

            def find(x):
                while p2[x] != x:
                    x = p2[x]
                return x
            a, b = find(e[0]), find(e[1])
            if a != b:
                p2[max(a, b)] = min(a, b)
                chosen.append(e)
                rec(idx + 1, chosen, p2)
                chosen.pop()
        rec(idx + 1, chosen, parent)
    rec(0, [], list(range(n)))
    return res


def tree_flats(T, n):
    """Partitions given by components of subforests of T."""
    out = set()
    m = len(T)
    for mask in range(1 << m):
        parent = list(range(n))

        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x
        for j in range(m):
            if mask >> j & 1:
                a, b = find(T[j][0]), find(T[j][1])
                parent[max(a, b)] = min(a, b)
        groups = {}
        for i in range(n):
            groups.setdefault(find(i), []).append(i)
        out.add(canon(groups.values(), n))
    return out
