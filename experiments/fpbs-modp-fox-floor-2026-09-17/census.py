#!/usr/bin/env python3
"""Census of the mod-p Fox floor k_u(V)/|V| on finite levels of F(a,b).

k_u = dim_Fp ker(I - P_c - P_cb), c = b a b^-2 (identity with B_direct is checked
in foxfloor.py).  Levels: random Schreier graphs, and regular (Cayley) levels of
SL_2 / PSL_2 quotients with the Sanov pair and with random pairs.
p = 2 uses bit-packed elimination; other p use foxfloor.rank_mod_p.
"""
import sys, random, itertools
import numpy as np
from foxfloor import rank_mod_p, word_perm, gens_of, inv_perm

def ops(A, B):
    g, n = gens_of(A, B)
    return word_perm('baBB', g, n), word_perm('baBBb', g, n)

def ku_p2(A, B):
    Pc, Pcb = ops(A, B)
    n = len(A)
    rows = []
    for v in range(n):
        r = (1 << v) ^ (1 << Pc[v]) ^ (1 << Pcb[v])
        rows.append(r)
    # rank over F2
    rank, basis = 0, {}
    for r in rows:
        while r:
            h = r.bit_length() - 1
            if h in basis:
                r ^= basis[h]
            else:
                basis[h] = r; rank += 1
                break
    return n - rank

def ku(A, B, p):
    if p == 2:
        return ku_p2(A, B)
    Pc, Pcb = ops(A, B)
    n = len(A)
    M = np.eye(n, dtype=np.int64)
    for v in range(n):
        M[v, Pc[v]] -= 1; M[v, Pcb[v]] -= 1
    return n - rank_mod_p(M, p)

def transitive(A, B):
    n = len(A); seen = {0}; st = [0]
    while st:
        v = st.pop()
        for w in (A[v], B[v]):
            if w not in seen:
                seen.add(w); st.append(w)
    return len(seen) == n

# ---- matrix-group Cayley levels -------------------------------------------
def mat_mul(X, Y, m):
    return ((X[0]*Y[0]+X[1]*Y[2]) % m, (X[0]*Y[1]+X[1]*Y[3]) % m,
            (X[2]*Y[0]+X[3]*Y[2]) % m, (X[2]*Y[1]+X[3]*Y[3]) % m)

def cayley(ga, gb, m, projective=False):
    def norm(X):
        if not projective:
            return X
        Y = tuple((-x) % m for x in X)
        return min(X, Y)
    e = norm((1, 0, 0, 1))
    idx = {e: 0}; elts = [e]; i = 0
    while i < len(elts):
        X = elts[i]; i += 1
        for g in (ga, gb):
            Y = norm(mat_mul(X, g, m))
            if Y not in idx:
                idx[Y] = len(elts); elts.append(Y)
    A = [idx[norm(mat_mul(X, ga, m))] for X in elts]
    B = [idx[norm(mat_mul(X, gb, m))] for X in elts]
    return A, B

if __name__ == '__main__':
    rng = random.Random(917)
    primes = [2, 3, 5, 7, 1000003]
    print('# random Schreier levels: n, p, mean k_u/n over transitive samples (max)')
    for n in (50, 100, 200, 400, 800):
        for p in primes:
            if p != 2 and n > 800:
                continue
            vals = []
            while len(vals) < (6 if n <= 200 else 3):
                A = list(range(n)); B = list(range(n)); rng.shuffle(A); rng.shuffle(B)
                if transitive(A, B):
                    vals.append(ku(A, B, p) / n)
            print(f'schreier n={n:5d} p={p:7d} mean={np.mean(vals):.4f} max={max(vals):.4f}')
        sys.stdout.flush()
    for n in (1600, 3200, 6400):
        vals = []
        for _ in range(3):
            while True:
                A = list(range(n)); B = list(range(n)); rng.shuffle(A); rng.shuffle(B)
                if transitive(A, B):
                    break
            vals.append(ku_p2(A, B) / n)
        print(f'schreier n={n:5d} p=2 mean={np.mean(vals):.4f} max={max(vals):.4f}')
        sys.stdout.flush()
    print('# Cayley levels G = <A,B> <= SL2(Z/m) (or PSL2), Sanov pair and random pairs')
    sanov = ((1, 2, 0, 1), (1, 0, 2, 1))
    for m in (3, 5, 7, 9, 11, 13):
        for proj in (False, True):
            pairs = [('sanov', sanov)] if m % 2 else []
            for k in range(2):
                while True:
                    X = tuple(rng.randrange(m) for _ in range(4)); Y = tuple(rng.randrange(m) for _ in range(4))
                    if (X[0]*X[3]-X[1]*X[2]) % m == 1 and (Y[0]*Y[3]-Y[1]*Y[2]) % m == 1:
                        break
                pairs.append((f'rand{k}', (X, Y)))
            for name, (ga, gb) in pairs:
                A, B = cayley(ga, gb, m, proj)
                n = len(A)
                if n > 2200:
                    continue
                res = []
                for p in primes:
                    res.append(f'{ku(A, B, p)}' )
                print(f'{"PSL2" if proj else "SL2"}(Z/{m}) {name:6s} |G|={n:5d} k_u(p=2,3,5,7,0)= {" ".join(res)}')
                sys.stdout.flush()
