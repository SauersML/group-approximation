"""Transition-digraph class sizes of lambda o (tau x sigma).

tau: strict automaton whose transition digraph is complete on k letters (any strict
automaton becomes such after composing with a translation, see the node).
sigma: an explicit bijective automaton over every group, with digraph S.
lambda: a letter permutation of A x B.
R(lambda o (tau x sigma)) = lambda-image of K_k (x) S, computed exactly here.
"""
import math, random, sys
from collections import Counter

sys.setrecursionlimit(100000)


def sccs(n, adj):
    idx, low, st, on, out, c = {}, {}, [], set(), [], [0]

    def dfs(v):
        idx[v] = low[v] = c[0]; c[0] += 1; st.append(v); on.add(v)
        for w in adj[v]:
            if w not in idx:
                dfs(w); low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == v:
                    break
            out.append(comp)

    for v in range(n):
        if v not in idx:
            dfs(v)
    return out


def classes(n, adj):
    comps = sccs(n, adj)
    on_cycle = all(len(c) > 1 or c[0] in adj[c[0]] for c in comps)
    return sorted(len(c) for c in comps), on_cycle


def product(k, B, S):
    L = [(a, b) for a in range(k) for b in B]
    ix = {l: i for i, l in enumerate(L)}
    R0 = {ix[(a, b)]: sorted({ix[(a2, b2)] for a2 in range(k) for b2 in S[b]}) for (a, b) in L}
    return L, R0


def shear_S(q, r):
    """sigma(x1,x2)(g) = (x1(g), x2(g) + x1(g s)), x1 in {0..q-1} (as integers), x2 in Z_r."""
    B = [(b1, b2) for b1 in range(q) for b2 in range(r)]
    return B, {b: sorted({(b[0], (b[1] + c) % r) for c in range(q)}) for b in B}


if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    q = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    r = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    trials = int(sys.argv[4]) if len(sys.argv) > 4 else 20000
    B, S = shear_S(q, r)
    L, R0 = product(k, B, S)
    n = len(L)
    random.seed(1)
    cnt = Counter(); example = {}
    for t in range(trials):
        lam = list(range(n)); random.shuffle(lam)
        adj = {i: [lam[j] for j in R0[i]] for i in range(n)}
        sizes, ok = classes(n, adj)
        g = 0
        for s in sizes:
            g = math.gcd(g, s)
        cnt[(ok, g)] += 1
        example.setdefault((ok, g), (sizes, lam))
    print("k", k, "B", len(B), "letters", n)
    for key in sorted(cnt):
        print(key, cnt[key], "e.g. sizes", example[key][0])
