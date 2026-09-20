"""Rank-3 target: the weak form deep >= c*law fails, with deep = 1 and law -> oo.

B = <a^2, b, a b a^-1>  (index 2 in F, rank 3),  A = <b, a^4, a b^2 a^-1> <= B.
Q_n = Z/n with a: i -> i+1, b = id.  For odd n:
  deep(Q_n) = 1: one seed (checked by exact search below; by hand, the chord
    a^n lies in S, and <K, a^n> contains a^n and every a^m b a^-m, hence K').
  law(Q_n) >= h(n) := dim_F2 coker( H_1(Gamma_A(Q_n)) -> H_1(Gamma_B(Q_n)) ),
    since each lawful merge adds one loop to the image of pi_1.
Also prints exact law for small n (BFS, capped).
Usage: python3 rank3_family.py nmax exact_cap
"""
import sys
from chains import analyse, pair_graphs, seeds_of, search
from foldlib import contains_kernel

A = ['b', 'aaaa', 'abbA']
B = ['aa', 'b', 'abA']


def edges(G):
    E = []
    for v in range(G.V):
        for (l, e), u in G.nb[v].items():
            if e == 1:
                E.append((v, l, u))
    return E


def cycle_basis(G):
    """Fundamental cycles as sets of edge indices (edges = edges(G))."""
    E = edges(G)
    adj = [[] for _ in range(G.V)]
    for i, (v, l, u) in enumerate(E):
        adj[v].append((u, i))
        adj[u].append((v, i))
    par = [None] * G.V
    pe = [None] * G.V
    tree = set()
    for r in range(G.V):
        if par[r] is not None:
            continue
        par[r] = r
        st = [r]
        while st:
            v = st.pop()
            for (u, i) in adj[v]:
                if par[u] is None:
                    par[u] = v
                    pe[u] = i
                    tree.add(i)
                    st.append(u)

    def path(v):
        out = set()
        while par[v] != v:
            out ^= {pe[v]}
            v = par[v]
        return out
    cyc = []
    for i, (v, l, u) in enumerate(E):
        if i not in tree:
            cyc.append(path(v) ^ path(u) ^ {i})
    return E, cyc


def rank_f2(vecs):
    basis = {}
    r = 0
    for x in vecs:
        while x:
            h = x.bit_length() - 1
            if h in basis:
                x ^= basis[h]
            else:
                basis[h] = x
                r += 1
                break
    return r


def coker_dim(PA, PB):
    GB, GA, m = pair_graphs(PA, PB, A, B)
    EB, cycB = cycle_basis(GB)
    idx = {(v, l): i for i, (v, l, u) in enumerate(EB)}
    EA, cycA = cycle_basis(GA)
    img = []
    for c in cycA:
        x = 0
        for i in c:
            v, l, u = EA[i]
            x ^= 1 << idx[(m[v], l)]
        img.append(x)
    return len(cycB) - rank_f2(img)


def main():
    nmax, cap = int(sys.argv[1]), int(sys.argv[2])
    for n in range(1, nmax + 1, 2):
        PA = [(i + 1) % n for i in range(n)]
        PB = list(range(n))
        GB, GA, m = pair_graphs(PA, PB, A, B)
        single = seeds_of(GA, m)
        one = [v[0] for v in single.values()]
        d1, w = search(GA, one, lambda c: contains_kernel(GA, c, m), 1)
        h = coker_dim(PA, PB)
        law = None
        if n <= 5:
            _, law = analyse(PA, PB, A, B, cap)[:2]
        print('n', n, 'deep<=1', d1 == 1, 'law_lower_h', h, 'law_exact', law,
              flush=True)


if __name__ == '__main__':
    main()
