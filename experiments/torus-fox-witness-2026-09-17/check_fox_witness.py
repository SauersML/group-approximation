#!/usr/bin/env python3
"""Fox witness for the failure of augmentation-only proofs of C2.

Claim checked (artifact research/artifacts/torus-degree-locally-indicable-and-fox-witness-2026-09-18.md, Sec. 3):
if H = <x_1..x_n | r_1..r_k> is perfect, J = Fox Jacobian (k x n, image in Z[H]),
E = eps(J) the exponent-sum matrix, and P in M_{n x k}(Z) with P E = I_n, then
D0 = P J satisfies eps(D0) = I_n and D0 c = 0 in Z[H]^n, where c = (x_i - 1)_i.
So D = D0^* (conjugate transpose) has eps(D) = I and the nonzero row c^* in its left kernel.

Part A: exact identity  sum_i (dr/dx_i)(x_i - 1) = r - 1  in Z[F] for every relator
        (Higman's group, A_5, BS(2,3)), and eps(D0) = I for the perfect ones.
Part B: finite perfect calibration K = A_5: build D0 over Z[A_5] from the presentation
        <x, y | x^2, y^3, (xy)^5>, and verify in the right regular representation that
        c^* D = 0 exactly and that D is singular over Q (rank < 2|K|).
Part C: BS(2,3) (locally indicable): the exponent-sum lattice has rank 1 < 2, so no P exists
        (consistent with Strebel / Howie--Schneebeli: no witness on a locally indicable group).
"""
from itertools import permutations
from fractions import Fraction
import sympy as sp
import numpy as np

# ---------- free group ring Z[F] ----------
def reduce_word(w):
    out = []
    for g, e in w:
        if out and out[-1][0] == g and out[-1][1] == -e:
            out.pop()
        else:
            out.append((g, e))
    return tuple(out)

def inv_word(w):
    return tuple((g, -e) for g, e in reversed(w))

def rmul(a, b):
    out = {}
    for u, cu in a.items():
        for v, cv in b.items():
            w = reduce_word(u + v)
            out[w] = out.get(w, 0) + cu * cv
    return {w: c for w, c in out.items() if c}

def radd(a, b, s=1):
    out = dict(a)
    for w, c in b.items():
        out[w] = out.get(w, 0) + s * c
    return {w: c for w, c in out.items() if c}

ONE = {(): 1}

def elt(w):
    return {reduce_word(w): 1}

def fox(r, i):
    """Left Fox derivative d r / d x_i in Z[F]."""
    out = {}
    for k, (g, e) in enumerate(r):
        if g != i:
            continue
        if e == 1:
            out = radd(out, elt(r[:k]))
        else:
            out = radd(out, elt(r[:k + 1]), -1)
    return out

def eps(a):
    return sum(a.values())

def expo(r, n):
    v = [0] * n
    for g, e in r:
        v[g] += e
    return v

def parse(s, names):
    """word string like 'B a b A A' with capitals = inverses."""
    w = []
    for t in s.split():
        if t.islower():
            w.append((names.index(t), 1))
        else:
            w.append((names.index(t.lower()), -1))
    return tuple(w)

def fox_identity_ok(rels, n):
    for r in rels:
        lhs = {}
        for i in range(n):
            lhs = radd(lhs, rmul(fox(r, i), radd(elt(((i, 1),)), ONE, -1)))
        if lhs != radd(elt(r), ONE, -1):
            return False
    return True

def integer_left_inverse(E):
    """P (n x k) over Z with P E = I_n, or None, by integer row reduction. E is k x n.
    Returns (P, pivots) where pivots are the diagonal entries of the echelon form."""
    k, n = len(E), len(E[0])
    H = [list(r) for r in E]
    U = [[1 if i == j else 0 for j in range(k)] for i in range(k)]
    row = 0
    piv = []
    for col in range(n):
        # Euclid on column col among rows >= row
        while True:
            nz = [i for i in range(row, k) if H[i][col] != 0]
            if not nz:
                break
            m = min(nz, key=lambda i: abs(H[i][col]))
            H[row], H[m] = H[m], H[row]; U[row], U[m] = U[m], U[row]
            done = True
            for i in range(row + 1, k):
                q = H[i][col] // H[row][col]
                if q:
                    H[i] = [a - q * b for a, b in zip(H[i], H[row])]
                    U[i] = [a - q * b for a, b in zip(U[i], U[row])]
                if H[i][col] != 0:
                    done = False
            if done:
                break
        if row < k and H[row][col] != 0:
            piv.append(H[row][col]); row += 1
        else:
            piv.append(0)
    if row < n or any(abs(d) != 1 for d in piv):
        return None, piv
    # back-substitute to make the top n x n block the identity
    for c in reversed(range(n)):
        if H[c][c] == -1:
            H[c] = [-a for a in H[c]]; U[c] = [-a for a in U[c]]
        for i in range(c):
            q = H[i][c]
            if q:
                H[i] = [a - q * b for a, b in zip(H[i], H[c])]
                U[i] = [a - q * b for a, b in zip(U[i], U[c])]
    P = sp.Matrix(U[:n])
    assert P * sp.Matrix(E) == sp.eye(n)
    return P, piv

def build_D0(rels, n, P):
    k = len(rels)
    J = [[fox(r, i) for i in range(n)] for r in rels]
    D0 = [[{} for _ in range(n)] for _ in range(n)]
    for a in range(n):
        for i in range(n):
            acc = {}
            for j in range(k):
                if P[a, j]:
                    acc = radd(acc, J[j][i], int(P[a, j]))
            D0[a][i] = acc
    return D0

# ---------- Part A ----------
print("Part A: Fox identity and eps(D0)")
names4 = ['a', 'b', 'c', 'd']
# Higman's group, repo convention b^a = b^2 i.e. a^{-1} b a b^{-2}
higman = [parse('A b a B B', names4), parse('B c b C C', names4),
          parse('C d c D D', names4), parse('D a d A A', names4)]
names2 = ['x', 'y']
a5 = [parse('x x', names2), parse('y y y', names2), parse('x y x y x y x y x y', names2)]
bs23 = [parse('Y x x y X X X', names2)]   # y^{-1} x^2 y = x^3
for label, rels, n in [('Higman', higman, 4), ('A5', a5, 2), ('BS(2,3)', bs23, 2)]:
    ok = fox_identity_ok(rels, n)
    E = [expo(r, n) for r in rels]
    P, diag = integer_left_inverse(E)
    line = f"  {label}: fox identity {'OK' if ok else 'FAIL'}; exponent-sum echelon pivots {diag}"
    if P is not None:
        D0 = build_D0(rels, n, P)
        epsD0 = sp.Matrix([[eps(D0[a][i]) for i in range(n)] for a in range(n)])
        line += f"; P={P.tolist()}; eps(D0)=I? {epsD0 == sp.eye(n)}"
    else:
        line += "; no integer P with P E = I (no Fox witness)"
    print(line)

# explicit Higman D0 rows (as words) for the artifact
P, _ = integer_left_inverse([expo(r, 4) for r in higman])
D0h = build_D0(higman, 4, P)
def show(a):
    def wstr(w):
        return ''.join(names4[g] if e == 1 else names4[g].upper() for g, e in w) or '1'
    return ' + '.join(f"{c}*{wstr(w)}" for w, c in sorted(a.items())) or '0'
print("  Higman D0 = P J (in Z[F], before reduction in H):")
for a in range(4):
    print("   row", a, ":", ' | '.join(show(D0h[a][i]) for i in range(4)))

# ---------- Part B: A_5 in the regular representation ----------
print("Part B: A_5 calibration in the right regular representation")
def pmul(p, q):  # apply p then q  (right action)
    return tuple(q[p[i]] for i in range(len(p)))
def pinv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)
idp = tuple(range(5))
X = (1, 0, 3, 2, 4)       # (0 1)(2 3)
Y = (2, 1, 4, 3, 0)       # (0 2 4)
# close under multiplication
K = {idp}
frontier = [idp]
while frontier:
    nxt = []
    for g in frontier:
        for s in (X, Y):
            h = pmul(g, s)
            if h not in K:
                K.add(h); nxt.append(h)
    frontier = nxt
K = sorted(K)
idx = {g: i for i, g in enumerate(K)}
N = len(K)
XY = pmul(X, Y)
def ppow(p, m):
    r = idp
    for _ in range(m):
        r = pmul(r, p)
    return r
assert ppow(X, 2) == idp and ppow(Y, 3) == idp and ppow(XY, 5) == idp
print(f"  |K| = {N}; relations x^2 = y^3 = (xy)^5 = 1 hold")
gens = [X, Y]
def word_to_perm(w):
    r = idp
    for g, e in w:
        r = pmul(r, gens[g] if e == 1 else pinv(gens[g]))
    return r
def R(a):  # right regular representation: v R(a) = coefficients of xi * a
    M = np.zeros((N, N), dtype=np.int64)
    for w, c in a.items():
        g = word_to_perm(w)
        for h in K:
            M[idx[h], idx[pmul(h, g)]] += c
    return M
P5, _ = integer_left_inverse([expo(r, 2) for r in a5])
D0 = build_D0(a5, 2, P5)
# D = D0^*: D_{ij} = (D0_{ji})^*
def star(a):
    out = {}
    for w, c in a.items():
        iw = inv_word(w)
        out[iw] = out.get(iw, 0) + c
    return out
D = [[star(D0[j][i]) for j in range(2)] for i in range(2)]
M = np.block([[R(D[i][j]) for j in range(2)] for i in range(2)])
cstar = [radd(elt(((i, -1),)), ONE, -1) for i in range(2)]
v = np.concatenate([np.eye(N, dtype=np.int64)[idx[idp]] @ R(cstar[i]) for i in range(2)])
print(f"  c^* != 0: {bool(np.any(v))};  c^* D == 0 exactly: {bool(np.all(v @ M == 0))}")
epsD = sp.Matrix([[eps(D[i][j]) for j in range(2)] for i in range(2)])
def rank_mod(A, p=1000003):
    A = [[int(x) % p for x in row] for row in A.tolist()]
    r = 0; rows = len(A); cols = len(A[0])
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i][c]), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        r += 1
    return r
rank = rank_mod(M)   # rank mod a large prime; rank over Q is at least this, and the exact
                     # kernel row c^* already proves rank_Q < 2|K|
rank_float = int(np.linalg.matrix_rank(M.astype(float)))
print(f"  eps(D) = {epsD.tolist()};  rank of D on Q[K]^2: mod-p {rank}, float {rank_float}, of {2 * N}")
