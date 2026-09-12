#!/usr/bin/env python3
# kh-cckw: fit entry polynomials of the U4 normal forms and verify candidate readouts (runs on MSI).
import itertools
p = 7; n = 4
def mul(A, B): return tuple(tuple(sum(A[i][t]*B[t][j] for t in range(n)) % p for j in range(n)) for i in range(n))
I = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
def E(entries):
    M = [list(r) for r in I]
    for (r, c), v in entries.items(): M[r][c] = (M[r][c] + v) % p
    return tuple(tuple(r) for r in M)
Va = E({(0,3):1, (1,2):1}); Vb = E({(1,0):1, (2,3):-1}); Vc = E({(3,1):1})
Vai = E({(0,3):-1, (1,2):-1}); Vbi = E({(1,0):-1, (2,3):1}); Vci = E({(3,1):-1})
INV = {Va: Vai, Vb: Vbi, Vc: Vci}
def pw(A, e):
    R = I
    for _ in range(e): R = mul(R, A)
    return R
def inv(A):
    if A in INV: return INV[A]
    R = I; B = A; e = 7**4 - 1
    while e:
        if e & 1: R = mul(R, B)
        B = mul(B, B); e >>= 1
    return R
def comm(x, y): return mul(mul(mul(inv(x), inv(y)), x), y)
monos = [m for m in itertools.product(range(3), repeat=4) if sum(m) <= 3]
def solve_mod(rows, rhs):
    # least-squares-free exact solve over F7 (consistent system), returns coefficient vector or None
    m = len(rows[0]); A = [list(r) + [b] for r, b in zip(rows, rhs)]; piv = []; r = 0
    for c in range(m):
        pr = next((i for i in range(r, len(A)) if A[i][c] % p), None)
        if pr is None: continue
        A[r], A[pr] = A[pr], A[r]; iv = pow(A[r][c], p-2, p); A[r] = [(v*iv) % p for v in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] % p:
                f = A[i][c]; A[i] = [(A[i][t] - f*A[r][t]) % p for t in range(m+1)]
        piv.append(c); r += 1
    if any(all(v % p == 0 for v in row[:m]) and row[m] % p for row in A): return None
    x = [0]*m
    for i, c in enumerate(piv): x[c] = A[i][m]
    return x
names = "ijkl"
def fmt(coefs):
    terms = []
    for co, m in zip(coefs, monos):
        if co: terms.append(f"{co}*" + "".join(names[t]*m[t] for t in range(4)) if sum(m) else f"{co}")
    return " + ".join(terms) or "0"
for label, x, y in [("<c,b>", Vc, Vb), ("<c,a>", Vc, Va)]:
    D = comm(x, y); Ee = comm(D, y)
    g = {t: mul(mul(mul(pw(x,t[0]), pw(y,t[1])), pw(D,t[2])), pw(Ee,t[3])) for t in itertools.product(range(7), repeat=4)}
    print("==", label, "D:", D, "E:", Ee)
    rows = [[(t[0]**m[0] * t[1]**m[1] * t[2]**m[2] * t[3]**m[3]) % p for m in monos] for t in g]
    for pos in itertools.product(range(4), repeat=2):
        rhs = [g[t][pos[0]][pos[1]] for t in g]
        if len(set(rhs)) > 1:
            co = solve_mod(rows, rhs)
            print("  M", pos, "=", fmt(co) if co else "NOT DEGREE<=3")
# candidate readouts
def rd_cb(M):
    i = M[3][1]; j = M[1][0]; k = (M[3][0] - i*j) % p; l = None
    return i, j, k, M
for label, x, y in [("<c,b>", Vc, Vb), ("<c,a>", Vc, Va)]:
    pass
print("x^7 = I for all normal-form elements (exponent 7):",
      all(pw(M, 7) == I for M in [mul(mul(mul(pw(Vc,t[0]), pw(Vb,t[1])), pw(comm(Vc,Vb),t[2])), pw(comm(comm(Vc,Vb),Vb),t[3])) for t in itertools.product(range(7), repeat=4)]))
