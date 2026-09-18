"""One-endedness certificates for the doubles D(F_2, C) that carry a Lemma 6 surface subgroup.

Lemma 7 of research/malnormal-free-doubles-surface-certificates-proof.md: let S = <A, Abar> be the
closed surface subgroup of genus >= 2 given by a certificate Y (A = pi_1(Y) <= F).  Put
    W = { u in F : A ∩ u A u^-1 != 1 }.
If A ∪ W generates F, then D(F_2, C) is one-ended.

For each certificate verified by verify_lemma6.py this script
  1. rebuilds Y and a basis of A = pi_1(Y, v0) from a spanning tree;
  2. for every reduced word u of length <= MAXLEN tests A ∩ u A u^-1 != 1 via the fibre product of
     the Stallings graphs of A and of u A u^-1, and checks the resulting witness h != 1 directly
     (h and u^-1 h u both read closed paths at the base of Gamma_A);
  3. iterates H_0 = A, H_{k+1} = <H_k ∪ W(H_k)> (Lemma 7 applies to any H_k fixing the vertex of S),
     and reports ONE-ENDED when some H_k has the rose on a, b as Stallings graph (H_k = F).
Usage: python3 one_ended_certificate.py out_pairs_r2.txt out_pairs_r3.txt
"""
import itertools
import sys

from verify_lemma6 import parse, build_Y, component, s_of, inv_word, inv_letter

MAXLEN = 4


def basis(Y, v0=0):
    """Words of a free basis of pi_1(Y, v0) (spanning tree by BFS)."""
    path = {v0: []}
    order = [v0]
    for v in order:
        for x, u in sorted(Y[v].items()):
            if u not in path:
                path[u] = path[v] + [x]
                order.append(u)
    gens = set()
    for v in path:
        for x, u in Y[v].items():
            if path[v] + [x] == path[u] or path[u] + [inv_letter(x)] == path[v]:
                continue  # tree edge
            g = reduce(path[v] + [x] + inv_word(path[u]))
            if tuple(inv_word(g)) not in gens:
                gens.add(tuple(g))
    return [list(g) for g in gens]


def reduce(w):
    out = []
    for x in w:
        if out and out[-1] == inv_letter(x):
            out.pop()
        else:
            out.append(x)
    return out


def fold(gens):
    """Stallings graph of <gens> (words as letter lists); returns (adj, base index)."""
    edges, nv = [], 1
    for g in gens:
        v = 0
        for i, x in enumerate(g):
            u = 0 if i == len(g) - 1 else nv
            if u == nv:
                nv += 1
            edges.append((v, x, u))
            v = u
    parent = list(range(nv))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    changed = True
    while changed:
        changed = False
        out = {}
        for (v, x, u) in edges:
            for key, tgt in (((find(v), x), find(u)), ((find(u), inv_letter(x)), find(v))):
                if key in out and find(out[key]) != find(tgt):
                    parent[find(out[key])] = find(tgt)
                    changed = True
                else:
                    out.setdefault(key, tgt)
    roots = sorted({find(v) for v in range(nv)})
    idx = {r: i for i, r in enumerate(roots)}
    adj = [dict() for _ in roots]
    for (v, x, u) in edges:
        a, b = idx[find(v)], idx[find(u)]
        assert adj[a].get(x, b) == b and adj[b].get(inv_letter(x), a) == a
        adj[a][x] = b
        adj[b][inv_letter(x)] = a
    return adj, idx[find(0)]


def read(G, v, w):
    for x in w:
        v = G[v].get(x)
        if v is None:
            return None
    return v


def nontrivial_intersection(A_gens, u):
    """Return a witness h != 1 with h in A and u^-1 h u in A, or None."""
    GA, a0 = fold(A_gens)
    Gu, u0 = fold([reduce(u + g + inv_word(u)) for g in A_gens])
    # spanning tree of the component of (a0, u0) in GA x Gu; a non-tree edge closes a loop
    start = (a0, u0)
    path = {start: []}
    order = [start]
    for P in order:
        for x, g2 in GA[P[0]].items():
            h2 = Gu[P[1]].get(x)
            if h2 is None:
                continue
            Q = (g2, h2)
            if Q not in path:
                path[Q] = path[P] + [x]
                order.append(Q)
    for P in order:
        for x, g2 in GA[P[0]].items():
            h2 = Gu[P[1]].get(x)
            if h2 is None:
                continue
            Q = (g2, h2)
            if path[P] + [x] == path[Q] or path[Q] + [inv_letter(x)] == path[P]:
                continue
            h = reduce(path[P] + [x] + inv_word(path[Q]))
            # the witness is checked directly, independently of the product computation
            if h and read(GA, a0, h) == a0 and read(GA, a0, reduce(inv_word(u) + h + u)) == a0:
                return h
            raise AssertionError("product loop is not a valid witness")
    return None


def certify(n, E, labels, max_rounds=6):
    """Iterate H_0 = A, H_{k+1} = <H_k, W(H_k)>; stop when H_k = F or H_k stops growing."""
    Y = build_Y(n, E, labels)
    A = basis(Y)
    H = A
    history = []
    for _ in range(max_rounds):
        W = []
        for L in range(1, MAXLEN + 1):
            for u in itertools.product(range(4), repeat=L):
                u = list(u)
                if any(u[i] == inv_letter(u[i + 1]) for i in range(L - 1)):
                    continue
                if nontrivial_intersection(H, u) is not None:
                    W.append(u)
        G, g0 = fold([g for g in H + W if g])
        history.append((len(G), len(W)))
        if len(G) == 1 and len(G[0]) == 4:
            return True, len(A), history
        newH = basis(G, g0)
        if len(G) == len(fold(H)[0]) and sorted(map(len, G)) == sorted(map(len, fold(H)[0])):
            return False, len(A), history
        H = newH
    return False, len(A), history


if __name__ == "__main__":
    seen = {}
    for path in sys.argv[1:]:
        for gens, cert in parse(path):
            n, E, labels = cert[:3]
            whole, rA, history = certify(n, E, labels)
            print(path, gens, "rank(A)", rA, "rounds (vertices of H_k, |W(H_k)|)", history,
                  "=> ONE-ENDED" if whole else "=> undecided")
            seen[gens] = seen.get(gens, False) or whole
            sys.stdout.flush()
    print("one-ended certified for", sum(seen.values()), "/", len(seen), "distinct C")
