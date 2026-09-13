# Operator-valued ChJN nested commutator: a = 1 + P(x)(alpha-1), b = 1 + Q(x)(beta-1)
# on V = W (x) k^5, alpha = (x a2 a3), beta = (x b2 b3). Exact rational arithmetic.
from fractions import Fraction as F
import random
random.seed(11)

def eye(n): return [[F(int(i == j)) for j in range(n)] for i in range(n)]
def mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)] for i in range(n)]
def add(A, B, s=1): return [[A[i][j] + s * B[i][j] for j in range(len(A[0]))] for i in range(len(A))]
def inv(A):
    n = len(A); M = [row[:] + e for row, e in zip(A, eye(n))]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]; M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]
def kron(A, B):
    return [[A[i // len(B)][j // len(B[0])] * B[i % len(B)][j % len(B[0])]
             for j in range(len(A[0]) * len(B[0]))] for i in range(len(A) * len(B))]
def perm(cycle, n=5):
    M = eye(n)
    for s in cycle:
        for r in range(n): M[r][s] = F(0)
    for i, s in enumerate(cycle): M[cycle[(i + 1) % len(cycle)]][s] = F(1)
    return M
def eq(A, B): return all(A[i][j] == B[i][j] for i in range(len(A)) for j in range(len(A[0])))

al, be, I5 = perm([0, 1, 2]), perm([0, 3, 4]), eye(5)
def c1(x, y): return mul(mul(x, y), mul(inv(x), inv(y)))
def c2(x, y): return mul(mul(inv(x), inv(y)), mul(x, y))
CM = {"c1": c1, "c2": c2}
CONV = None

def nested(P, Q, first, conv=None):
    cm = CM[conv or CONV]
    n = len(P); I = eye(5 * n)
    A = add(I, kron(P, add(al, I5, -1))); B = add(I, kron(Q, add(be, I5, -1)))
    if first == "a": return cm(cm(inv(B), inv(A)), cm(B, A)), I
    return cm(cm(inv(A), inv(B)), cm(A, B)), I

def coeff(N, I, S, n):
    D = add(N, I, -1)
    X = [[None] * n for _ in range(n)]
    ok = True
    for i in range(n):
        for j in range(n):
            blk = [row[j * 5:(j + 1) * 5] for row in D[i * 5:(i + 1) * 5]]
            # blk must be X_ij * S exactly: read the ratio at the (1,0) entry of S (S[1][0] = 1)
            r0, s0 = next((r, c) for r in range(5) for c in range(5) if S[r][c] != 0)
            lam = blk[r0][s0] / S[r0][s0]
            X[i][j] = lam
            if not eq(blk, [[lam * s for s in row] for row in S]): ok = False
    return X, ok

one = [[F(1)]]
targets = {"al": al, "al^-1": inv(al), "be": be, "be^-1": inv(be)}
for conv in CM:
    Na, _ = nested(one, one, "a", conv); Nb, _ = nested(one, one, "b", conv)
    print("conv", conv, "order-a =", [k for k, v in targets.items() if eq(Na, v)], "order-b =", [k for k, v in targets.items() if eq(Nb, v)])
    if eq(Na, al) and eq(Nb, be) and CONV is None: CONV = conv
print("using", CONV)

def rand_idem(n, r):
    while True:
        S = [[F(random.randint(-3, 3)) for _ in range(n)] for _ in range(n)]
        try: Si = inv(S); break
        except StopIteration: pass
    d = [[F(int(i == j and i < r)) for j in range(n)] for i in range(n)]
    return mul(mul(S, d), Si)

cases = [("common-kernel", [[F(1), F(0)], [F(0), F(0)]], [[F(1), F(0)], [F(2), F(0)]]),
         ("common-image", [[F(1), F(0)], [F(0), F(0)]], [[F(1), F(2)], [F(0), F(0)]])]
for t in range(4): cases.append(("rand n=2 r=1 #%d" % t, rand_idem(2, 1), rand_idem(2, 1)))
for t in range(2): cases.append(("rand n=3 r=2 #%d" % t, rand_idem(3, 2), rand_idem(3, 1)))
for name, P, Q in cases:
    n = len(P)
    words = {"PQ": mul(P, Q), "QP": mul(Q, P), "PQP": mul(mul(P, Q), P), "QPQ": mul(mul(Q, P), Q)}
    commute = eq(mul(P, Q), mul(Q, P))
    Na, I = nested(P, Q, "a"); Xa, oka = coeff(Na, I, add(al, I5, -1), n)
    Nb, I = nested(P, Q, "b"); Xb, okb = coeff(Nb, I, add(be, I5, -1), n)
    ma = [w for w, v in words.items() if oka and eq(Xa, v)]
    mb = [w for w, v in words.items() if okb and eq(Xb, v)]
    print(name, "commute:", commute, "| a-order coefficient form:", oka, "matches", ma,
          "| b-order coefficient form:", okb, "matches", mb)
    if not oka: print("   a-order D block (0,0):", [[str(x) for x in row] for row in add(Na, I, -1)[0:5]])
print("DONE")
