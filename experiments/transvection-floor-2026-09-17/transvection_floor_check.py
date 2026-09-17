#!/usr/bin/env python3
"""Check the transvection floor on complex permutation modules of SL_n(F_q).

Claim (transvection-floor-kills-ambient-rank-transfers): for n >= 3, every complex
representation psi of SL_n(F_q) (q = p^e) and every transvection t,
    rank(psi(t) - 1) >= c(p,q) * (N - dim V^G),   c(p,q) = (1 - 1/p)(1 - 1/q)/2 >= 1/8,
and N - dim V^G >= rank(psi(y) - 1) for every y.  The sharper intermediate bound is
    N - dim V^U >= (1 - 1/q)(N - dim V^G)/2   for the root subgroup U = {1 + a E_12}.

For a permutation module C[X]: rank(y - 1) = |X| - #cycles(y), dim V^G = #orbits,
dim V^U = #U-orbits.  We enumerate the whole group, act on several G-sets X and report
    ratio  = rank(t - 1) / (N - #orbits)          (must be >= c(p,q))
    ratioU = (N - #U-orbits) / (N - #orbits)       (must be >= (1 - 1/q)/2)
    maxy   = max_y rank(y - 1) / (N - #orbits)     (must be <= 1; max over ALL y in G)
Calibration: the natural F_q-module is NOT a complex representation, and there
rank(t - 1)/rank(y - 1) = 1/n; the floor needs characteristic != p.
Run: nice -n 10 timeout 1200 python3 transvection_floor_check.py
"""
import itertools, sys


def field(q):
    """Addition and multiplication tables of F_q, q in {2, 3, 4}."""
    if q in (2, 3):
        add = [[(a + b) % q for b in range(q)] for a in range(q)]
        mul = [[(a * b) % q for b in range(q)] for a in range(q)]
        return q, add, mul
    if q == 4:  # F_4 = F_2[w]/(w^2 + w + 1), elements as bit pairs
        def m(a, b):
            r = 0
            for i in range(2):
                if (b >> i) & 1:
                    r ^= a << i
            if r & 4:
                r ^= 0b111
            return r
        return 2, [[a ^ b for b in range(4)] for a in range(4)], [[m(a, b) for b in range(4)] for a in range(4)]
    raise ValueError(q)


def run(n, q):
    p, add, mul = field(q)
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [None] + [next(b for b in range(q) if mul[a][b] == 1) for a in range(1, q)]

    def det(M):
        m = len(M)
        if m == 1:
            return M[0][0]
        tot = 0
        for j in range(m):
            if M[0][j] == 0:
                continue
            minor = [row[:j] + row[j + 1:] for row in M[1:]]
            term = mul[M[0][j]][det(minor)]
            if j % 2:
                term = neg[term]
            tot = add[tot][term]
        return tot

    vecs = list(itertools.product(range(q), repeat=n))
    vidx = {v: i for i, v in enumerate(vecs)}
    V = len(vecs)
    vadd = [[vidx[tuple(add[x][y] for x, y in zip(u, w))] for w in vecs] for u in vecs]
    smul = [[vidx[tuple(mul[a][x] for x in u)] for u in vecs] for a in range(q)]

    G = [rows for rows in itertools.product(vecs, repeat=n) if det([list(r) for r in rows]) == 1]

    def vec_perm(A):
        cols = [vidx[tuple(A[i][k] for i in range(n))] for k in range(n)]
        out = []
        for v in vecs:
            acc = 0
            for k in range(n):
                if v[k]:
                    acc = vadd[acc][smul[v[k]][cols[k]]]
            out.append(acc)
        return out

    def normalize(v):
        for x in v:
            if x:
                return tuple(mul[inv[x]][y] for y in v)

    points = sorted({normalize(v) for v in vecs if any(v)})
    pidx = {x: i for i, x in enumerate(points)}
    P = len(points)
    vec2pt = [pidx[normalize(v)] if any(v) else None for v in vecs]
    pt2vec = [vidx[x] for x in points]
    lines = sorted({frozenset(vec2pt[vadd[smul[a][pt2vec[i]]][smul[b][pt2vec[j]]]]
                              for a in range(q) for b in range(q) if (a, b) != (0, 0))
                    for i in range(P) for j in range(P) if i != j}, key=sorted)
    lidx = {L: i for i, L in enumerate(lines)}
    flags = [(x, i) for i, L in enumerate(lines) for x in sorted(L)]
    fidx = {f: i for i, f in enumerate(flags)}

    def all_perms(A):
        pv = vec_perm(A)
        pp = [vec2pt[pv[pt2vec[i]]] for i in range(P)]
        pl = [lidx[frozenset(pp[x] for x in L)] for L in lines]
        out = {'vectors': pv, 'points': pp, 'lines': pl,
               'flags': [fidx[(pp[x], pl[i])] for (x, i) in flags]}
        if V * V <= 800:
            out['vector-pairs'] = [pv[u] * V + pv[w] for u in range(V) for w in range(V)]
        if P * P <= 2000:
            out['point-pairs'] = [pp[u] * P + pp[w] for u in range(P) for w in range(P)]
        return out

    def E(i, j, a):
        return tuple(tuple(1 if r == c else (a if (r, c) == (i, j) else 0) for c in range(n)) for r in range(n))

    gens = [E(i, j, a) for i in range(n) for j in range(n) if i != j for a in range(1, q)]
    U = [E(0, 1, a) for a in range(1, q)]
    t = E(0, 1, 1)
    names = list(all_perms(t).keys())

    def orbits(perms, N):
        parent = list(range(N))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        for Pm in perms:
            for i, j in enumerate(Pm):
                ri, rj = find(i), find(j)
                if ri != rj:
                    parent[ri] = rj
        return len({find(i) for i in range(N)})

    def cycles(Pm):
        N = len(Pm)
        seen = bytearray(N)
        c = 0
        for i in range(N):
            if not seen[i]:
                c += 1
                j = i
                while not seen[j]:
                    seen[j] = 1
                    j = Pm[j]
        return c

    tp = all_perms(t)
    gp = [all_perms(g) for g in gens]
    up = [all_perms(u) for u in U]
    Ns = {k: len(tp[k]) for k in names}
    maxrank = {k: 0 for k in names}
    for A in G:
        pa = all_perms(A)
        for k in names:
            r = Ns[k] - cycles(pa[k])
            if r > maxrank[k]:
                maxrank[k] = r
    cp = (1 - 1 / p) * (1 - 1 / q) / 2
    bad = []
    for k in names:
        N = Ns[k]
        orbG = orbits([g[k] for g in gp], N)
        orbU = orbits([u[k] for u in up], N)
        rank_t = N - cycles(tp[k])
        denom = N - orbG
        ratio, ratioU, maxy = rank_t / denom, (N - orbU) / denom, maxrank[k] / denom
        ok = ratio >= cp - 1e-12 and ratioU >= (1 - 1 / q) / 2 - 1e-12 and maxy <= 1 + 1e-12
        print(f"SL_{n}(F_{q}) |G|={len(G)} X={k:12s} N={N:5d} orbits={orbG} rank(t-1)={rank_t:5d} "
              f"ratio={ratio:.4f} (floor {cp:.4f}) ratioU={ratioU:.4f} (floor {(1-1/q)/2:.4f}) "
              f"maxy={maxy:.4f} {'OK' if ok else 'VIOLATION'}", flush=True)
        if not ok:
            bad.append((n, q, k))
    return bad


if __name__ == '__main__':
    bad = []
    for (n, q) in [(3, 2), (3, 3), (4, 2), (3, 4)]:
        bad += run(n, q)
    print('violations:', bad)
    sys.exit(1 if bad else 0)
