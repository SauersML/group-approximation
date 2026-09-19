"""Probe of the perfect branch for Own(B_1, 2) on F_2 (exploratory, not a proof).

Shell pattern: the f/s perfect point P rooted at 1, on W = B_{n+2} minus B_n.
Center pattern on E2 = B_1: the translate of P rooted at g, for several g.
Question: is there a PERFECT completion (every vertex of T = B_{n+1} claimed, claims inside radius 1)?
By the shell-waste identity any completion is automatically perfect on T, so this is just a matching test.
"""
import itertools
import networkx as nx
from shell_waste_check import GENS, mul, ball, perfect_point


def word_mul(u, v):
    for g in v:
        u = mul(u, g)
    return u


def inv(w):
    from shell_waste_check import INV
    return "".join(INV[c] for c in reversed(w))


def translated_center(g, P):
    """Pattern on B_1 of the point v -> g P(g^-1 v)."""
    out = {}
    for v in ball(1):
        u = word_mul(inv(g), v)
        out[v] = tuple(word_mul(g, c) for c in P[u])
    return out


def deficiency(n, center, P):
    Q, T = ball(n), ball(n + 1)
    W = ball(n + 2) - Q
    fixed = {w: P[w] for w in W}
    fixed.update(center)
    used = set()
    for c in fixed.values():
        for u in c:
            if u in used:
                return None
            used.add(u)
    free = sorted(Q - set(center))
    G = nx.Graph()
    left = [(w, i) for w in free for i in (0, 1)]
    G.add_nodes_from(left)
    for w in free:
        for u in [w] + [mul(w, g) for g in GENS]:
            if u in T and u not in used:
                for i in (0, 1):
                    G.add_edge((w, i), ("t", u))
    m = nx.bipartite.maximum_matching(G, top_nodes=left)
    return len(left) - sum(1 for x in left if x in m)


if __name__ == "__main__":
    n = 5
    P = perfect_point(12)
    gs = sorted(w for w in ball(4) if len(w) <= 4)
    res = {}
    for g in gs:
        d = deficiency(n, translated_center(g, P), P)
        res[d] = res.get(d, 0) + 1
    print("n =", n, "center translates g in B_4: deficiency histogram", res)
