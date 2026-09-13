#!/usr/bin/env python3.11
# Model test for congruence-relator-width part 1: Lemmas 2.1, 2.2 (linear algebra over F_p)
# and Lemma 3.1 (brute-force Hensel covering in small congruence groups).
import itertools, sys

def mul(A, B, m):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) % m for j in range(n)] for i in range(n)]

def ident(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]

def mpow(A, e, m):
    R, P = ident(len(A)), A
    while e:
        if e & 1: R = mul(R, P, m)
        P = mul(P, P, m); e >>= 1
    return R

def det(A, m):
    n = len(A)
    if n == 1: return A[0][0] % m
    return sum((-1) ** j * A[0][j] * det([r[:j] + r[j+1:] for r in A[1:]], m) for j in range(n)) % m

def inv_mod_p(A, p):
    n = len(A); M = [row[:] + ident(n)[i] for i, row in enumerate(A)]
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] % p)
        M[c], M[piv] = M[piv], M[c]; iv = pow(M[c][c], -1, p)
        M[c] = [x * iv % p for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c]; M[r] = [(x - f * y) % p for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]

def rank_mod_p(rows, p):
    rows = [r[:] for r in rows]; rk = 0; ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((r for r in range(rk, len(rows)) if rows[r][c] % p), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]; iv = pow(rows[rk][c], -1, p)
        rows[rk] = [x * iv % p for x in rows[rk]]
        for r in range(len(rows)):
            if r != rk and rows[r][c]:
                f = rows[r][c]; rows[r] = [(x - f * y) % p for x, y in zip(rows[r], rows[rk])]
        rk += 1
    return rk

def primes(N):
    out, d = [], 2
    while d * d <= N:
        if N % d == 0:
            out.append(d)
            while N % d == 0: N //= d
        d += 1
    if N > 1: out.append(N)
    return out

def singer(n, p):
    N = p ** n - 1
    for coeffs in itertools.product(range(p), repeat=n):
        if coeffs[0] == 0: continue
        C = [[0] * n for _ in range(n)]
        for i in range(1, n): C[i][i-1] = 1
        for i in range(n): C[i][n-1] = (-coeffs[i]) % p
        if mpow(C, N, p) != ident(n): continue
        if all(mpow(C, N // l, p) != ident(n) for l in primes(N)):
            return mpow(C, p - 1, p)
    raise RuntimeError("no primitive polynomial")

def comm_rows(S, n, p):
    # linear conditions X S - S X = 0 on X (n^2 unknowns)
    rows = []
    for i in range(n):
        for j in range(n):
            row = [0] * (n * n)
            for k in range(n):
                row[i * n + k] = (row[i * n + k] + S[k][j]) % p
                row[k * n + j] = (row[k * n + j] - S[i][k]) % p
            rows.append(row)
    return rows

def sl_basis(n):
    B = []
    for i in range(n):
        for j in range(n):
            if i != j:
                M = [[0] * n for _ in range(n)]; M[i][j] = 1; B.append(M)
    for i in range(n - 1):
        M = [[0] * n for _ in range(n)]; M[i][i] = 1; M[n-1][n-1] = -1; B.append(M)
    return B

def lam_rank(sigmas, n, p):
    rows = []
    for S in sigmas:
        Si = inv_mod_p(S, p)
        for Y in sl_basis(n):
            Z = mul(mul(S, Y, p), Si, p)
            rows.append([(Z[i][j] - Y[i][j]) % p for i in range(n) for j in range(n)])
    return rank_mod_p(rows, p)

def partA():
    ok = True
    for p in (2, 3, 5, 7):
        for n in range(2, 7):
            if p ** n > 200000 or (n == 2 and p == 2): continue
            s1 = singer(n, p)
            if n >= 3:
                s = ident(n); s[0][1] = 1
            else:
                s = next(S for S in ([[a, b], [c, d]] for a, b, c, d in itertools.product(range(p), repeat=4))
                         if (S[0][0] * S[1][1] - S[0][1] * S[1][0]) % p == 1
                         and n * n - rank_mod_p(comm_rows(s1, n, p) + comm_rows(mul(mul(S, s1, p), inv_mod_p(S, p), p), n, p), p) == 1)
            s2 = mul(mul(s, s1, p), inv_mod_p(s, p), p)
            cdim = n * n - rank_mod_p(comm_rows(s1, n, p) + comm_rows(s2, n, p), p)
            r2, r1 = lam_rank([s1, s2], n, p), lam_rank([s1], n, p)
            good = cdim == 1 and r2 == n * n - 1
            ok &= good
            print(f"A n={n} p={p} det1={det(s1,p)} common-centralizer-dim={cdim} rank(two)={r2} rank(one)={r1} target={n*n-1} {'OK' if good else 'FAIL'}")
    # necessity of order prime to p: regular unipotent J and J^T when p | n
    for n, p in ((4, 2), (3, 3), (6, 2)):
        J = ident(n)
        for i in range(n - 1): J[i][i+1] = 1
        JT = [list(r) for r in zip(*J)]
        cdim = n * n - rank_mod_p(comm_rows(J, n, p) + comm_rows(JT, n, p), p)
        print(f"A-unipotent n={n} p={p} common-centralizer-dim={cdim} rank(J,JT)={lam_rank([J, JT], n, p)} target={n*n-1}")
    return ok

def lift_sl(S, m, p):
    g = [row[:] for row in S]
    d = det(g, m)
    u = pow(d, -1, m)  # d ≡ 1 mod p, so u ≡ 1 mod p
    g = [[(g[i][j] * (u if j == 0 else 1)) % m for j in range(len(g))] for i in range(len(g))]
    assert det(g, m) == 1
    return g

def inv_sl(g, m):
    n = len(g)
    if n == 2: return [[g[1][1] % m, -g[0][1] % m], [-g[1][0] % m, g[0][0] % m]]
    return mpow(g, order(g, m) - 1, m)

def order(g, m):
    k, P, I = 1, g, ident(len(g))
    while P != I: P = mul(P, g, m); k += 1
    return k

def partB(n, p, k):
    m = p ** k
    s1 = singer(n, p)
    if n >= 3: s = ident(n); s[0][1] = 1
    else:
        s = next(S for S in ([[a, b], [c, d]] for a, b, c, d in itertools.product(range(p), repeat=4))
                 if (S[0][0] * S[1][1] - S[0][1] * S[1][0]) % p == 1
                 and n * n - rank_mod_p(comm_rows(s1, n, p) + comm_rows(mul(mul(S, s1, p), inv_mod_p(S, p), p), n, p), p) == 1)
    s2 = mul(mul(s, s1, p), inv_mod_p(s, p), p)
    g1, g2 = lift_sl(s1, m, p), lift_sl(s2, m, p)
    g1i, g2i = inv_sl(g1, m), inv_sl(g2, m)
    K1 = []
    for ent in itertools.product(range(0, m, p), repeat=n * n):
        g = [[(int(i == j) + ent[i * n + j]) % m for j in range(n)] for i in range(n)]
        if det(g, m) == 1: K1.append(g)
    key = lambda g: tuple(x for r in g for x in r)
    inv = {key(b): inv_sl(b, m) for b in K1}
    c1 = [mul(mul(mul(g1, b, m), g1i, m), inv[key(b)], m) for b in K1]
    c2 = [mul(mul(mul(g2, b, m), g2i, m), inv[key(b)], m) for b in K1]
    img = {key(mul(x, y, m)) for x in c1 for y in c2}
    cover1 = {key(x) for x in c1}
    good = img == {key(b) for b in K1}
    print(f"B SL_{n}(Z/{m}) |K_1|={len(K1)} |[g1,K1][g2,K1]|={len(img)} |[g1,K1]|={len(cover1)} {'OK' if good else 'FAIL'}")
    return good

if __name__ == "__main__":
    ok = partA()
    for n, p, k in ((3, 2, 2), (2, 3, 2), (2, 3, 3), (2, 5, 2)):
        ok &= partB(n, p, k)
    print("ALL", "OK" if ok else "FAIL")
    print("DONE")
