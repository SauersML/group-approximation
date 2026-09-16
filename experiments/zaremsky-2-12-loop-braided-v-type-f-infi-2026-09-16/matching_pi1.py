#!/usr/bin/env python3
"""Certificates that small matching-type complexes are simply connected.

The complexes are flag complexes, so pi_1 is presented by the 2-skeleton:
  * generators: the edges;
  * relators: the edges of a spanning tree, and every triangle.
Greedy certificate: start with the tree edges as "trivial". Whenever a triangle has exactly one
non-trivial edge, that edge is trivial in pi_1 as well. If every edge becomes trivial, pi_1 = 1.
This is sound but may be inconclusive, in which case we print the rank of H_1 over GF(2)
(a nonzero rank proves pi_1 != 1).

Complexes:
  OM(K_n): vertices are ordered pairs (a, b), a != b, in {1..n}; simplices are families of
           pairwise disjoint pairs (the strict fundamental domain Q for PLB_n on L_n(LB_*));
  M(K_n):  the unordered version;
  M(L_n):  matchings of the linear graph (the fundamental domain for the pure system).
"""
import itertools
import sys


def om_kn(n, ordered=True):
    verts = list(itertools.permutations(range(n), 2)) if ordered else list(itertools.combinations(range(n), 2))
    adj = lambda u, v: len(set(u) | set(v)) == 4
    return verts, adj


def m_ln(n):
    verts = list(range(n - 1))  # edge {k, k+1}
    adj = lambda u, v: abs(u - v) >= 2
    return verts, adj


def certificate(verts, adj):
    idx = {v: i for i, v in enumerate(verts)}
    N = len(verts)
    nbrs = [[] for _ in range(N)]
    edges = {}
    for i, j in itertools.combinations(range(N), 2):
        if adj(verts[i], verts[j]):
            nbrs[i].append(j)
            nbrs[j].append(i)
            edges[(i, j)] = len(edges)
    # connectivity + BFS tree
    seen = [False] * N
    seen[0] = True
    stack = [0]
    trivial = set()
    while stack:
        u = stack.pop()
        for v in nbrs[u]:
            if not seen[v]:
                seen[v] = True
                trivial.add(edges[(min(u, v), max(u, v))])
                stack.append(v)
    if not all(seen):
        return {"vertices": N, "edges": len(edges), "connected": False}
    tris = []
    nset = [set(x) for x in nbrs]
    for (i, j), e in edges.items():
        for k in nbrs[j]:
            if k > j and k in nset[i]:
                tris.append((e, edges[(j, k)], edges[(i, k)]))
    changed = True
    while changed:
        changed = False
        for t in tris:
            rest = [e for e in t if e not in trivial]
            if len(rest) == 1:
                trivial.add(rest[0])
                changed = True
    out = {"vertices": N, "edges": len(edges), "triangles": len(tris), "connected": True,
           "pi1_trivial_certified": len(trivial) == len(edges)}
    if len(trivial) != len(edges):
        out["h1_rank_gf2"] = h1_rank_gf2(N, edges, tris)
    return out


def h1_rank_gf2(N, edges, tris):
    E = len(edges)
    # rank of boundary d1 : C1 -> C0 is N - 1 for a connected complex
    # rank of d2 : C2 -> C1 by Gaussian elimination over GF(2), rows as python ints
    basis = {}
    for t in tris:
        row = 0
        for e in t:
            row ^= 1 << e
        while row:
            h = row.bit_length() - 1
            if h in basis:
                row ^= basis[h]
            else:
                basis[h] = row
                break
    return E - (N - 1) - len(basis)


def main():
    for n in range(5, 10):
        v, a = om_kn(n, ordered=True)
        print(f"OM(K_{n}):", certificate(v, a))
    for n in range(5, 10):
        v, a = om_kn(n, ordered=False)
        print(f"M(K_{n}):", certificate(v, a))
    for n in range(5, 13):
        v, a = m_ln(n)
        print(f"M(L_{n}):", certificate(v, a))


if __name__ == "__main__":
    sys.exit(main())
