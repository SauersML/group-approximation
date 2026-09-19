"""Finite check of the shell-waste obstruction for the ownership SFT Own(B_1, 2) on F_2.

A point assigns to every vertex g of the Cayley tree of F_2 = <a, b> two distinct vertices of the closed
ball B_1(g) (its "claims"), with claims of distinct vertices disjoint.

The script checks, for n = 2..MAXN:
  1. the explicit perfect point P (f/s types, rooted at 1) claims every vertex of B_N exactly once;
  2. the shell-waste identity |T| - |K| - 2|Q| = 0 for Q = B_n, T = B_{n+1}, K = claims of the shell
     W = B_{n+2} minus B_n that land in T (P is perfect on T);
  3. with the shell pattern of P on W and the "away from 1" pattern p2 on E2 = B_1 (vertex 1 unclaimed),
     the free vertices B_n minus B_1 admit NO claims completing a point (max matching deficiency > 0);
  4. control: with P's own pattern on E2 instead of p2, the free vertices DO admit a completion.
Run: python3 shell_waste_check.py
"""
import networkx as nx

GENS = "aAbB"
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def mul(w, g):
    if w and w[-1] == INV[g]:
        return w[:-1]
    return w + g


def ball(n):
    out, frontier = {""}, {""}
    for _ in range(n):
        new = set()
        for w in frontier:
            for g in GENS:
                v = mul(w, g)
                if v not in out:
                    new.add(v)
        out |= new
        frontier = new
    return out


def children(w):
    """Neighbours of w one step farther from 1, in a fixed order."""
    return [w + g for g in GENS if not (w and w[-1] == INV[g])]


def perfect_point(N):
    """Claims of every vertex of B_{N-1} in the f/s perfect point rooted at 1."""
    typ = {"": "s"}
    claims = {}
    order = sorted(ball(N - 1), key=len)
    for w in order:
        ch = children(w)
        if typ[w] == "f":           # claimed by its parent: claim 2 children (type f), 3rd child type s
            claims[w] = (ch[0], ch[1])
            typ[ch[0]] = typ[ch[1]] = "f"
            for c in ch[2:]:
                typ[c] = "s"
        else:                       # claims itself and its first child (type f); other children type s
            claims[w] = (w, ch[0])
            typ[ch[0]] = "f"
            for c in ch[1:]:
                typ[c] = "s"
    return claims


def away_pattern():
    """p2 on E2 = B_1: every vertex claims its first two children away from 1; vertex 1 is unclaimed."""
    return {w: tuple(children(w)[:2]) for w in ball(1)}


def completion_deficiency(n, center):
    N = n + 3
    P = perfect_point(N)
    Q, T = ball(n), ball(n + 1)
    W = ball(n + 2) - Q
    fixed = {w: P[w] for w in W}
    fixed.update(center)
    used = set()
    for w, c in fixed.items():
        for u in c:
            assert u not in used, "fixed claims collide"
            used.add(u)
    free = sorted(Q - set(center))
    G = nx.Graph()
    left = [(w, i) for w in free for i in (0, 1)]
    G.add_nodes_from(left, bipartite=0)
    for w in free:
        nbrs = [w] + [mul(w, g) for g in GENS]
        for u in nbrs:
            if u in T and u not in used:
                for i in (0, 1):
                    G.add_edge((w, i), ("t", u))
    m = nx.bipartite.maximum_matching(G, top_nodes=left)
    matched = sum(1 for x in left if x in m)
    return len(left) - matched


def main(MAXN=6):
    for n in range(2, MAXN + 1):
        N = n + 3
        P = perfect_point(N)
        cover = {}
        for w, c in P.items():
            for u in c:
                assert u not in cover, ("collision", u)
                cover[u] = w
            for u in c:
                assert u == w or u in [mul(w, g) for g in GENS]
        assert all(u in cover for u in ball(N - 1)), "P not perfect"
        Q, T = ball(n), ball(n + 1)
        W = ball(n + 2) - Q
        K = {u for w in W for u in P[w] if u in T}
        waste = len(T) - len(K) - 2 * len(Q)
        d_bad = completion_deficiency(n, away_pattern())
        d_ctrl = completion_deficiency(n, {w: P[w] for w in ball(1)})
        print(f"n={n} |Q|={len(Q)} |T|={len(T)} |K|={len(K)} waste={waste} "
              f"deficiency(p2)={d_bad} deficiency(control)={d_ctrl}")
        assert waste == 0 and d_bad > 0 and d_ctrl == 0


if __name__ == "__main__":
    main()
