#!/usr/bin/env python3
"""Test deterministic left-order domination
    D:  I(x_1 ; y_F | x_{<1}) <= H(y_1)
for linear codes y_g = L (x_{ge})_{e in E} over F_p, x_g uniform in F_p^k, on Z (usual order) and on
F_2 = <a,b> (Magnus bi-order: a -> 1+X, b -> 1+Y, sign of leading deg-lex coefficient of w - 1).
Entropies in units log p are ranks. After deleting past columns, I = rank(M) - rank(M without x_1 columns).
usage: left_order_linear_domination.py z|f p k r 'E' R trials [structured]"""
import itertools, random, sys


def rank_mod(rows, p):
    M = [list(r) for r in rows]
    rk, ncol = 0, (len(M[0]) if M else 0)
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c] % p), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [v * inv % p for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] % p:
                t = M[i][c]
                M[i] = [(u - t * v) % p for u, v in zip(M[i], M[rk])]
        rk += 1
    return rk


# ---- free group words: tuples over {1,-1,2,-2}
def mul(u, v):
    u = list(u)
    for s in v:
        if u and u[-1] == -s:
            u.pop()
        else:
            u.append(s)
    return tuple(u)


def ball(R):
    out, frontier = {()}, [()]
    for _ in range(R):
        nf = []
        for w in frontier:
            for s in (1, -1, 2, -2):
                z = mul(w, (s,))
                if z not in out:
                    out.add(z); nf.append(z)
        frontier = nf
    return sorted(out, key=lambda w: (len(w), w))


def series_mul(A, B, D):
    C = {}
    for m1, c1 in A.items():
        for m2, c2 in B.items():
            if len(m1) + len(m2) <= D:
                m = m1 + m2
                C[m] = C.get(m, 0) + c1 * c2
    return {m: c for m, c in C.items() if c}


def gen_series(s, D):
    v = 'X' if abs(s) == 1 else 'Y'
    if s > 0:
        return {(): 1, (v,): 1}
    return {(v,) * n: (-1) ** n for n in range(D + 1)}


def magnus_sign(w, D):
    S = {(): 1}
    for s in w:
        S = series_mul(S, gen_series(s, D), D)
    S[()] = S.get((), 0) - 1
    nz = sorted((m for m, c in S.items() if c), key=lambda m: (len(m), m))
    if not nz:
        assert w == ()
        return 0
    return 1 if S[nz[0]] > 0 else -1


def parse_E(kind, s):
    if kind == 'z':
        return [int(t) for t in s.split(',')]
    m = {'a': 1, 'A': -1, 'b': 2, 'B': -2}
    return [tuple(m[c] for c in t if c != '1') for t in s.split(',')]


def main():
    kind, p, k, r = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    E, R, trials = parse_E(kind, sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
    structured = len(sys.argv) > 8
    if kind == 'z':
        F = list(range(-R, R + 1)); op = lambda g, h: g + h; one = 0
        sites = sorted(set(f + e for f in F for e in E) | {0}); sign = lambda g: (g > 0) - (g < 0)
    else:
        F = ball(R); op = mul; one = ()
        sites = sorted(set(mul(f, e) for f in F for e in E) | {()}, key=lambda w: (len(w), w))
        D = max(len(w) for w in sites) + 1
        cache = {w: magnus_sign(w, D) for w in sites}; sign = cache.get
    future = [g for g in sites if sign(g) >= 0]
    col = {g: i for i, g in enumerate(future)}
    rng = random.Random(7)
    worst = None
    for t in range(trials):
        L = [[rng.randrange(p) for _ in range(k * len(E))] for _ in range(r)]
        if structured:  # identity at E[0]; first row sees the other positions only through one symbol
            for i in range(r):
                for j in range(k * len(E)):
                    L[i][j] = 0
            L[0][0] = 1; L[0][k] = 1           # u.x_{e0} + x_{e1}[0]
            L[1][1] = 1; L[1][2 * k] = 1       # x_{e0}[1] + x_{e2}[0]
            for i in range(r):
                for j in range(k, k * len(E)):
                    if rng.random() < 0.5:
                        L[i][j] = rng.randrange(p)
        hy = rank_mod(L, p)
        rows = []
        for f in F:
            for i in range(r):
                row = [0] * (k * len(future))
                for ei, e in enumerate(E):
                    g = op(f, e)
                    if g in col:
                        for j in range(k):
                            row[k * col[g] + j] = (row[k * col[g] + j] + L[i][k * ei + j]) % p
                rows.append(row)
        full = rank_mod(rows, p)
        c1 = col[one]
        rest = [[v for j, v in enumerate(row) if j // k != c1] for row in rows]
        I = full - rank_mod(rest, p)
        gap = I - hy
        if worst is None or gap > worst[0]:
            worst = (gap, I, hy, L)
        if gap > 0:
            print('VIOLATION I=%d H(y1)=%d L=%s' % (I, hy, L)); break
    print('%s p=%d k=%d r=%d E=%s R=%d |F|=%d sites=%d worst I-H(y1)=%d (I=%d rankL=%d)'
          % (kind, p, k, r, sys.argv[5], R, len(F), len(sites), worst[0], worst[1], worst[2]))


if __name__ == '__main__':
    main()
