#!/usr/bin/env python3
"""Check the CCKW Proposition 7.15 matrices for GHB(p) (block size k, F_p entries):
1. the eleven relators of GHB(p) hold for (a,b,c) -> (V'a, V'b, V'c);
2. the orders of the three vertex subgroups <a,b>, <c,b>, <c,a> of the image
   (injectivity on the vertex groups U3(p), U4(p), U4(p) means orders p^3, p^4, p^4).
CCKW commutator convention [x,y] = x^-1 y^-1 x y, left-normed [x,y,z] = [[x,y],z].
Usage: kms_quotient_check.py <p> <k> <seed> [trials]
"""
import random
import sys

p = int(sys.argv[1]); k = int(sys.argv[2]); seed = int(sys.argv[3])
trials = int(sys.argv[4]) if len(sys.argv) > 4 else 1
n = 4 * k


def mat_mul(A, B):
    return tuple(tuple(sum(A[i][t] * B[t][j] for t in range(n)) % p for j in range(n))
                 for i in range(n))


def ident():
    return tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))


def mat_pow(A, e):
    R = ident(); B = A
    while e:
        if e & 1:
            R = mat_mul(R, B)
        B = mat_mul(B, B); e >>= 1
    return R


def inverse(A):
    # A is unipotent-ish; compute inverse via A^(order-1) is expensive; use Gauss-Jordan mod p
    M = [list(A[i]) + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] % p)
        M[col], M[piv] = M[piv], M[col]
        inv = pow(M[col][col], p - 2, p)
        M[col] = [(v * inv) % p for v in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [(M[r][t] - f * M[col][t]) % p for t in range(2 * n)]
    return tuple(tuple(M[i][n:]) for i in range(n))


def comm(x, y):
    return mat_mul(mat_mul(mat_mul(inverse(x), inverse(y)), x), y)


def block(entries):
    """entries: dict (bi,bj) -> k x k list-matrix; identity on diagonal blocks."""
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        out[i][i] = 1
    for (bi, bj), M in entries.items():
        for r in range(k):
            for c in range(k):
                out[bi * k + r][bj * k + c] = (out[bi * k + r][bj * k + c] + M[r][c]) % p
    return tuple(tuple(row) for row in out)


def neg(M):
    return [[(-v) % p for v in row] for row in M]


def closure_order(gens, cap=200000):
    seen = {ident()}
    frontier = [ident()]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mat_mul(x, g)
                if y not in seen:
                    seen.add(y); nxt.append(y)
                    if len(seen) > cap:
                        return None
        frontier = nxt
    return len(seen)


rng = random.Random(seed)
for t in range(trials):
    if k == 1 and t == 0:
        Ma = [[1]]; Mb = [[1]]; Mc = [[1]]
    else:
        Ma = [[rng.randrange(p) for _ in range(k)] for _ in range(k)]
        Mb = [[rng.randrange(p) for _ in range(k)] for _ in range(k)]
        Mc = [[rng.randrange(p) for _ in range(k)] for _ in range(k)]
    Va = block({(0, 3): Ma, (1, 2): Ma})
    Vb = block({(1, 0): Mb, (2, 3): neg(Mb)})
    Vc = block({(3, 1): Mc})
    I = ident()
    rels = {
        "a^p": mat_pow(Va, p), "b^p": mat_pow(Vb, p), "c^p": mat_pow(Vc, p),
        "[a,b,a]": comm(comm(Va, Vb), Va), "[a,b,b]": comm(comm(Va, Vb), Vb),
        "[c,b,c]": comm(comm(Vc, Vb), Vc), "[c,b,b,c]": comm(comm(comm(Vc, Vb), Vb), Vc),
        "[c,b,b,b]": comm(comm(comm(Vc, Vb), Vb), Vb),
        "[c,a,c]": comm(comm(Vc, Va), Vc), "[c,a,a,c]": comm(comm(comm(Vc, Va), Va), Vc),
        "[c,a,a,a]": comm(comm(comm(Vc, Va), Va), Va),
    }
    bad = [name for name, M in rels.items() if M != I]
    oab = closure_order([Va, Vb]); ocb = closure_order([Vc, Vb]); oca = closure_order([Vc, Va])
    print(f"trial {t}: p={p} k={k} relators failing: {bad or 'none'}; "
          f"|<a,b>|={oab} (want {p**3}), |<c,b>|={ocb} (want {p**4}), |<c,a>|={oca} (want {p**4})")
    if not bad and oab == p ** 3 and ocb == p ** 4 and oca == p ** 4:
        print("INJECTIVE ON ALL THREE VERTEX GROUPS", "Ma", Ma, "Mb", Mb, "Mc", Mc)
