"""Calibration for nonsingular-magnus-extremes-separable-piece-sofic.

BS(2,3): window relation x_{j+1}^2 = x_j^3.  Over a FIXED finite alphabet Q,
a bi-infinite configuration lives on the maximal subgraph of the edge relation
u -> v (v^2 = u^3) in which every vertex has an in-edge and an out-edge.  The
proof (section 9) predicts that every edge of that core joins commuting
elements, so [a, t^-1 a t] dies at every coordinate.  This script checks the
prediction exhaustively for Q = S_3..S_6.  It is a check of the lemma, not of
the theorem.  Usage: python3 bs23_fixed_alphabet.py
"""
from itertools import permutations

def mul(p, q):  # (p*q)(i) = p(q(i))
    return tuple(p[i] for i in q)

def power(p, k):
    r = tuple(range(len(p)))
    for _ in range(k):
        r = mul(p, r)
    return r

def check(n):
    G = list(permutations(range(n)))
    sq = {g: power(g, 2) for g in G}
    cu = {g: power(g, 3) for g in G}
    by_sq = {}
    for g in G:
        by_sq.setdefault(sq[g], []).append(g)
    edges = {u: by_sq.get(cu[u], []) for u in G}
    alive = set(G)
    changed = True
    while changed:
        changed = False
        has_in = set()
        for u in alive:
            for v in edges[u]:
                if v in alive:
                    has_in.add(v)
        new = {u for u in alive if u in has_in and any(v in alive for v in edges[u])}
        if new != alive:
            alive, changed = new, True
    bad = [(u, v) for u in alive for v in edges[u] if v in alive and mul(u, v) != mul(v, u)]
    return len(G), len(alive), len(bad)

if __name__ == "__main__":
    for n in range(3, 7):
        order, core, bad = check(n)
        print(f"S_{n}: |Q|={order} core={core} noncommuting core edges={bad}")
