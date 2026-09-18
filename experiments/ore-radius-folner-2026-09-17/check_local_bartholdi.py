#!/usr/bin/env python3
"""Sanity checks for `ore-radius-function-bounds-folner-radius` (swarm-0917, c-famen).

Pure Python, no dependencies. Run: python3 check_local_bartholdi.py

1. Bartholdi's cycle set system (arXiv:1605.09133v2, Lemma 2.1): for n = 3..6,
   #Y = H_n n!  and  #(X_i minus union of X_j, j in I-{i}) = n!/#I  for all i in I.
2. The slack inequality n!(1 + ln n - H_n) >= 1 for 3 <= n <= 400 (then monotone).
3. Genericity demo for n = 3 (r = 12): random alpha_s over GF(p) make every stacked
   map (alpha_{s,T_s})_s with sum #X_{s,T_s} >= r injective. (A demo; the proof uses
   Schwartz-Zippel, not random sampling.)
4. End-to-end local lemma on G = Z, S = {0,1,2}: kernel vectors of the (r-1) x r
   matrix M' = sum_t alpha_t t over GF(p)[Z] exist on windows of length >= 22, and every
   one found has support F with |S+F| < (1 + ln 3)|F|.
5. Calibration on the non-amenable free product C2*C2*C2 with S = {1,x,y,z}
   (n = 4, r = 51): no kernel vector supported in the ball of radius 1, where
   |S B(1)| = 10 >= (1 + ln 4) * 4.
"""
import itertools
import math
import random

P = 1_000_003


def cycles_system(n):
    """Y = cycles of permutations of {0..n-1} (with multiplicity over permutations)."""
    Y = []  # each point: frozenset of the cycle's elements
    for perm in itertools.permutations(range(n)):
        seen = set()
        for i in range(n):
            if i in seen:
                continue
            cyc = []
            j = i
            while j not in seen:
                seen.add(j)
                cyc.append(j)
                j = perm[j]
            Y.append(frozenset(cyc))
    return Y


def check_counts():
    for n in range(3, 7):
        Y = cycles_system(n)
        H = sum(1 / i for i in range(1, n + 1))
        assert abs(len(Y) - H * math.factorial(n)) < 1e-6, (n, len(Y))
        for size in range(1, n + 1):
            for I in itertools.combinations(range(n), size):
                for i in I:
                    others = set(I) - {i}
                    cnt = sum(1 for y in Y if i in y and not (others & y))
                    assert cnt * size == math.factorial(n), (n, I, i, cnt)
        print(f"[1] n={n}: #Y={len(Y)} = H_n n!, private counts n!/#I verified")


def check_slack():
    H = 1.0
    for n in range(2, 401):
        H += 1 / n
        if n >= 3:
            x = 1 + math.log(n) - H
            assert x > 0 and math.lgamma(n + 1) + math.log(x) >= 0, n
    print("[2] n!(1+ln n-H_n) >= 1 for 3<=n<=400 (and 1+ln n-H_n increases in n)")


def rank_mod_p(rows, ncols):
    rows = [r[:] for r in rows]
    rank = 0
    col = 0
    nrows = len(rows)
    for col in range(ncols):
        piv = None
        for i in range(rank, nrows):
            if rows[i][col] % P:
                piv = i
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], P - 2, P)
        rows[rank] = [(v * inv) % P for v in rows[rank]]
        for i in range(nrows):
            if i != rank and rows[i][col] % P:
                f = rows[i][col]
                rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[rank])]
        rank += 1
    return rank, rows


def nullspace_mod_p(rows, ncols):
    rank, red = rank_mod_p(rows, ncols)
    pivots = []
    for r in red[:rank]:
        pivots.append(next(c for c in range(ncols) if r[c] % P))
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for r, pc in zip(red[:rank], pivots):
            v[pc] = (-r[fc]) % P
        basis.append(v)
    return basis


def build_alphas(n, rng):
    """Y' = cycles plus one extra point '*'; alpha_s : K^{Y'} -> K^{X_s} generic."""
    Y = cycles_system(n) + [None]
    r = len(Y)
    X = [[idx for idx, y in enumerate(Y) if y is not None and s in y] for s in range(n)]
    alpha = []
    for s in range(n):
        A = [[0] * r for _ in range(r)]
        for row in X[s]:
            for c in range(r):
                A[row][c] = rng.randrange(P)
        alpha.append(A)
    return Y, r, X, alpha


def check_genericity(rng):
    n = 3
    Y, r, X, alpha = build_alphas(n, rng)
    checked = 0
    for Ts in itertools.product(*[[set(T) for k in range(1, n + 1)
                                   for T in itertools.combinations(range(n), k) if s in T]
                                  for s in range(n)]):
        priv = []
        for s in range(n):
            others = Ts[s] - {s}
            priv.append([row for row in X[s] if not any(row in X[t] for t in others)])
        if sum(len(p) for p in priv) < r:
            continue
        stacked = [alpha[s][row] for s in range(n) for row in priv[s]]
        rank, _ = rank_mod_p(stacked, r)
        assert rank == r
        checked += 1
    print(f"[3] n=3, r={r}: {checked} families with sum #X_(s,T_s) >= r, all injective")
    return Y, r, X, alpha


def local_lemma_on_Z(Y, r, alpha):
    S = [0, 1, 2]
    star = r - 1  # the extra point, a zero row of M
    found = 0
    for L in (21, 22, 26, 30):
        window = list(range(L + 1))
        out = list(range(L + 3))
        rows = []
        for g in out:
            for i in range(r):
                if i == star:
                    continue
                row = [0] * (r * len(window))
                for t_idx, t in enumerate(S):
                    h = g - t  # Theta(phi)(g) = sum_t alpha_t phi(g - t)
                    if 0 <= h <= L:
                        for j in range(r):
                            row[h * r + j] = (row[h * r + j] + alpha[t_idx][i][j]) % P
                rows.append(row)
        basis = nullspace_mod_p(rows, r * len(window))
        if not basis:
            print(f"[4] Z, window [0,{L}]: no kernel vector")
            continue
        rng = random.Random(L)
        for _ in range(3):
            v = [0] * (r * len(window))
            for b in basis:
                c = rng.randrange(P)
                v = [(a + c * x) % P for a, x in zip(v, b)]
            F = {h for h in window if any(v[h * r + j] for j in range(r))}
            SF = {h + t for h in F for t in S}
            assert F and len(SF) < (1 + math.log(3)) * len(F), (L, len(F), len(SF))
            found += 1
        print(f"[4] Z, window [0,{L}]: kernel dim {len(basis)}, sampled kernel supports obey |S+F| < (1+ln 3)|F|")
    assert found


def free_product_calibration(rng):
    n = 4
    Y, r, X, alpha = build_alphas(n, rng)
    star = r - 1
    # elements of C2*C2*C2 as reduced words over 'xyz'
    def mul(a, b):
        w = list(a)
        for ch in b:
            if w and w[-1] == ch:
                w.pop()
            else:
                w.append(ch)
        return ''.join(w)
    ball = ['']
    frontier = ['']
    for _ in range(1):
        nxt = []
        for w in frontier:
            for ch in 'xyz':
                u = mul(w, ch)
                if len(u) > len(w):
                    nxt.append(u)
        ball += nxt
        frontier = nxt
    S = ['', 'x', 'y', 'z']
    index = {w: k for k, w in enumerate(ball)}
    out = sorted({mul(s, h) for s in S for h in ball})
    rows = []
    for g in out:
        for i in range(r):
            if i == star:
                continue
            row = [0] * (r * len(ball))
            for t_idx, t in enumerate(S):
                h = mul(t, g)  # t^-1 g with t an involution
                if h in index:
                    k = index[h]
                    for j in range(r):
                        row[k * r + j] = (row[k * r + j] + alpha[t_idx][i][j]) % P
            rows.append(row)
    rank, _ = rank_mod_p(rows, r * len(ball))
    assert rank == r * len(ball)
    print(f"[5] C2*C2*C2, S={{1,x,y,z}}, r={r}, window B(1) ({len(ball)} elements, |S B(1)|={len(out)}): no kernel vector")


if __name__ == "__main__":
    rng = random.Random(20260917)
    check_counts()
    check_slack()
    Y, r, X, alpha = check_genericity(rng)
    local_lemma_on_Z(Y, r, alpha)
    free_product_calibration(rng)
    print("all checks passed")
