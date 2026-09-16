#!/usr/bin/env python3
"""One-pivot paths inside X-apartments between P = {12,34,...} and rho P = {23,45,...,n1} in the diagonal link X_n.

Usage: python3 x_apartment_pivot.py n

Search space: all proper noncrossing partitions v of U_n (vertices of X_n) and all noncrossing spanning trees T of
U_n (apartments of B_n contained in X_n, HKS Proposition 4.4; a partition lies in the apartment of T iff each of its
blocks, singletons included, induces a connected subgraph of T).
Method: for each v, test whether some tree contains P and v, and whether some tree contains v and rho P. If both hold
and cos d_B(P, v) + cos d_B(v, rho P) > 0, the broken geodesic P -> v -> rho P lies in X_n and has length < pi, so
d_X(P, rho P) < pi and (Proposition S of the 2026-09-16 artifact) X_n is not CAT(1).
By the hemisphere lemma (Lemma H) a pivot at a non-vertex point z of a face sigma, with sigma sharing an X-apartment
with P and with rho P, exists only if some vertex of sigma passes the same test, so vertices suffice for one pivot.
Output: counts, and the best value of the sum over v sharing X-apartments with both endpoints.
"""
import sys, math, itertools

n = int(sys.argv[1]); m = n - 1
popc = lambda v: bin(v).count("1")

def set_partitions(n):
    def rec(i, blocks):
        if i == n:
            yield blocks; return
        for k in range(len(blocks)):
            nb = list(blocks); nb[k] |= (1 << i)
            yield from rec(i + 1, nb)
        yield from rec(i + 1, blocks + [1 << i])
    yield from rec(0, [])

def chords_cross(e, f):
    a, b = sorted(e); c, d = sorted(f)
    if len({a, b, c, d}) < 4:
        return False
    return (a < c < b) != (a < d < b)

def crossing_blocks(b1, b2):
    e1 = [i for i in range(n) if b1 >> i & 1]; e2 = [i for i in range(n) if b2 >> i & 1]
    return any(chords_cross(x, y) for x in itertools.combinations(e1, 2) for y in itertools.combinations(e2, 2))

NC = []
for bl in set_partitions(n):
    ns = [b for b in bl if popc(b) >= 2]
    if all(not crossing_blocks(ns[i], ns[j]) for i in range(len(ns)) for j in range(i + 1, len(ns))):
        NC.append(tuple(sorted(bl)))
proper = [p for p in NC if 1 < len(p) < n]

# noncrossing spanning trees
edges = list(itertools.combinations(range(n), 2))
trees = []
def dfs(start, chosen, parent):
    if len(chosen) == n - 1:
        trees.append(list(chosen)); return
    for t in range(start, len(edges)):
        e = edges[t]
        if any(chords_cross(e, f) for f in chosen):
            continue
        par = list(parent)
        def find(a):
            while par[a] != a:
                a = par[a]
            return a
        ra, rb = find(e[0]), find(e[1])
        if ra == rb:
            continue
        par[ra] = rb
        dfs(t + 1, chosen + [e], par)
dfs(0, [], list(range(n)))

def connected_in(block, tree):
    el = [i for i in range(n) if block >> i & 1]
    if len(el) == 1:
        return True
    adj = {i: [] for i in el}
    for a, b in tree:
        if a in adj and b in adj:
            adj[a].append(b); adj[b].append(a)
    seen = {el[0]}; st = [el[0]]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w); st.append(w)
    return len(seen) == len(el)

def in_tree(part, tree):
    return all(connected_in(b, tree) for b in part)

def parse_pairs(shift):
    bl = [sum(1 << ((2 * t + i + shift) % n) for i in range(2)) for t in range(n // 2)]
    return tuple(sorted(bl))
P, Q = parse_pairs(0), parse_pairs(1)
TP = [T for T in trees if in_tree(P, T)]
TQ = [T for T in trees if in_tree(Q, T)]

def nblocks_join(x, y):
    parent = list(range(n))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    for bl in list(x) + list(y):
        el = [i for i in range(n) if bl >> i & 1]
        for t in el[1:]:
            parent[find(t)] = find(el[0])
    return len(set(find(i) for i in range(n)))

def cosd(x, z):
    a, b = n - len(x), n - len(z)
    k = n - len(x) - len(z) + nblocks_join(x, z)
    return (k - a * b / m) / math.sqrt((a - a * a / m) * (b - b * b / m))

fmt = lambda p: "{" + ",".join("".join(str(i + 1) for i in range(n) if b >> i & 1) for b in p if popc(b) >= 2) + "}"
both, best = [], (-9, None)
nE = 0
for v in proper:
    s = cosd(P, v) + cosd(v, Q)
    if s > 1e-12:
        nE += 1
    aP = any(in_tree(v, T) for T in TP)
    aQ = any(in_tree(v, T) for T in TQ)
    if aP and aQ:
        both.append(v)
        if s > best[0]:
            best = (s, v)
print("n =", n, "| noncrossing spanning trees:", len(trees), "| trees containing P:", len(TP), "| containing rho P:", len(TQ))
print("#proper vertices:", len(proper), "| #vertices with cos d(P,v)+cos d(v,rhoP) > 0:", nE)
print("#vertices sharing an X-apartment with P and with rho P:", len(both))
if best[1] is not None:
    s, v = best
    print("max of cos d(P,v)+cos d(v,rhoP) over those: %.6f at v = %s | path length %.6f pi" % (
        s, fmt(v), (math.acos(cosd(P, v)) + math.acos(cosd(v, Q))) / math.pi))
    print("ONE-PIVOT PATH SHORTER THAN PI EXISTS:", s > 1e-12)
