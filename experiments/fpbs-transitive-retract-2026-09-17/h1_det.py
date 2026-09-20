"""det of H_1(K') -> H_1(S) on finite L-sets Q.

S = Stab_L(0), K' = Stab_{L_j}(0) = S cap L_j, L = F(a,b), L_j = <a, t_j>,
t_j = phi^j(b), phi: a -> a, b -> b a b^-2.

Computed as the chain map H_1(Y) -> H_1(X). X is the Schreier graph of Q
(edges q -x-> q.x, x in {a,b}); Y is the Schreier graph of the L_j-set Q
(edges a and t_j), with each t_j-edge sent to its path in X. Coordinates are
the non-tree edges of BFS spanning trees. Only L_j-transitive Q are used
(then rk K' = rk S = n+1 and the matrix is square).

Usage: python3 h1_det.py j nmax_exhaustive n_random samples seed
"""
import sys
import random
import itertools
from fractions import Fraction

SUB = {'a': 'a', 'A': 'A', 'b': 'baBB', 'B': 'bbAB'}


def reduce(w):
    st = []
    for x in w:
        if st and st[-1] == x.swapcase():
            st.pop()
        else:
            st.append(x)
    return ''.join(st)


def tword(j):
    w = 'b'
    for _ in range(j):
        w = reduce(''.join(SUB[x] for x in w))
    return w


def det(M):
    n = len(M)
    M = [[Fraction(v) for v in r] for r in M]
    d = Fraction(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f:
                for k in range(c, n):
                    M[r][k] -= f * M[c][k]
    return int(d)


def bfs_tree(n, edges):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    seen = {0}
    tree = set()
    qu = [0]
    for u in qu:
        for v, i in adj[u]:
            if v not in seen:
                seen.add(v)
                tree.add(i)
                qu.append(v)
    return tree, seen, adj


def run(n, pa, pb, T):
    """Return det, or None if Q is not transitive, or 'intrans' if Q is not
    L_j-transitive."""
    perm = {'a': pa, 'b': pb}
    inv = {x: [0] * n for x in 'ab'}
    for x in 'ab':
        for q in range(n):
            inv[x][perm[x][q]] = q
    # X edge ids: a-edge at q is q, b-edge at q is n + q
    Xe = [(q, pa[q]) for q in range(n)] + [(q, pb[q]) for q in range(n)]
    Xtree, Xseen, _ = bfs_tree(n, Xe)
    if len(Xseen) < n:
        return None
    tperm, tchain = [], []
    for q in range(n):
        ch = {}
        p = q
        for x in T:
            if x in 'ab':
                e = (0 if x == 'a' else n) + p
                ch[e] = ch.get(e, 0) + 1
                p = perm[x][p]
            else:
                p2 = inv[x.lower()][p]
                e = (0 if x == 'A' else n) + p2
                ch[e] = ch.get(e, 0) - 1
                p = p2
        tperm.append(p)
        tchain.append(ch)
    Ye = [(q, pa[q]) for q in range(n)] + [(q, tperm[q]) for q in range(n)]
    Ytree, Yseen, Yadj = bfs_tree(n, Ye)
    if len(Yseen) < n:
        return 'intrans'
    pot = {0: {}}
    qu = [0]
    for u in qu:
        for v, i in Yadj[u]:
            if i in Ytree and v not in pot:
                c = dict(pot[u])
                s = 1 if Ye[i][0] == u else -1
                c[i] = c.get(i, 0) + s
                pot[v] = c
                qu.append(v)
    Xnt = [e for e in range(2 * n) if e not in Xtree]
    Xcol = {e: k for k, e in enumerate(Xnt)}
    rows = []
    for i in range(2 * n):
        if i in Ytree:
            continue
        u, v = Ye[i]
        cyc = dict(pot[u])
        cyc[i] = cyc.get(i, 0) + 1
        for e, c in pot[v].items():
            cyc[e] = cyc.get(e, 0) - c
        vec = [0] * len(Xnt)
        for e, c in cyc.items():
            if not c:
                continue
            ch = {e: 1} if e < n else tchain[e - n]
            for xe, xc in ch.items():
                if xe in Xcol:
                    vec[Xcol[xe]] += c * xc
        rows.append(vec)
    return det(rows)


def main():
    j, nmax, nr, samples, seed = map(int, sys.argv[1:6])
    T = tword(j)
    print('j =', j, 't_j =', T)
    # sanity: w17-pull example Q = Z/3, a = +1, b = -1, j = 1: |det| = 4
    if j == 1:
        print('Z/3 check:', run(3, [1, 2, 0], [2, 0, 1], T))
    for n in range(2, nmax + 1):
        hist = {}
        perms = list(itertools.permutations(range(n)))
        for pa in perms:
            for pb in perms:
                d = run(n, list(pa), list(pb), T)
                if d is None or d == 'intrans':
                    continue
                hist[abs(d)] = hist.get(abs(d), 0) + 1
        print('exhaustive n=%d |det| histogram:' % n, dict(sorted(hist.items())))
    rng = random.Random(seed)
    hist = {}
    for _ in range(samples):
        pa = list(range(nr))
        pb = list(range(nr))
        rng.shuffle(pa)
        rng.shuffle(pb)
        d = run(nr, pa, pb, T)
        if d is None or d == 'intrans':
            continue
        hist[abs(d)] = hist.get(abs(d), 0) + 1
    print('random n=%d |det| histogram:' % nr, dict(sorted(hist.items())))


if __name__ == '__main__':
    main()
