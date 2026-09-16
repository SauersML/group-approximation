#!/usr/bin/env python3
"""Exact split-module certificates for the ten CCKW trivalent triangle groups of the artifact
research/artifacts/split-module-triangles-of-finite-groups-2026-09-16.md, section 7.

Scope. The vertex presentations <x,y | R> of the groups G_0^{16,16,48}, G_0^{16,16,54}, G_0^{16,40,48},
G_0^{48,48,48}, G_0^{48,54,54}, G_8^{48,54,54}, G_0^{54,54,54}, G_2^{54,54,54} (cckw*_q.g) and
G_0^{16,16,40}, G_1^{16,16,48} (cckw334_yes.g), read from experiments/cckw-vtf-certificates/.

Method (exact arithmetic in Q(w), w^2 + w + 1 = 0; no floating point).
 1. Abstract vertex order |B| by coset enumeration (sympy, via vertex_split.vertex_group).
 2. Candidate matrices X, Y for x, y from four families:
      refl(k): X = diag(w,1)^(+-1),  Y = (I + (w-1) u v^T)^(+-1), u = (k,1)^T, v = (1,1-k), k in {1/3, 2/3};
      A5 augmentation module of two 3-cycles in S5 (basis e_i - e_5);
      monomial C3 wr C3: {X,Y} = {P^(+-1), diag(1,1,w)^(+-1)}, P the cyclic permutation matrix.
    Accept the first candidate satisfying every vertex relator exactly whose generated matrix group has
    order |B| (exact enumeration). Then M: B -> GL_n(Q(w)) is faithful (S1).
 3. (S2): dim M^x + dim M^y = n and M^x + M^y = Q(w)^n (exact ranks).
 4. Eigenvalue multiplicities of x and y on [x,M], [y,M] (ranks of X - w, X - w^2).
 5. At each vertex W_v = M + conj(M), plus lambda + conj(lambda) for a linear character lambda with
    delta = 0 when needed to balance dim [x,W_v] = dim [y,W_v]; relators checked on lambda exactly.
    Since W_v is closed under complex conjugation, [x,W_v] = (w + w^2)^(d_v/2) as a C3-module, whatever
    generator of the edge group is used; d = lcm(d_v) copies give (S3).
Command: timeout 600 python3 exact_vertex_modules.py > exact_vertex_modules.out 2>&1
"""
import os
for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
import itertools, math
from fractions import Fraction as Fr
from vertex_split import parse, vertex_words, vertex_group, perm_elements


class E:
    """a + b w in Q(w)."""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def __add__(self, o):
        return E(self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        return E(self.a - o.a, self.b - o.b)

    def __mul__(self, o):
        return E(self.a * o.a - self.b * o.b, self.a * o.b + self.b * o.a - self.b * o.b)

    def conj(self):  # w -> w^2 = -1 - w
        return E(self.a - self.b, -self.b)

    def inv(self):
        n = self.a * self.a - self.a * self.b + self.b * self.b
        c = self.conj()
        return E(c.a / n, c.b / n)

    def iszero(self):
        return self.a == 0 and self.b == 0

    def key(self):
        return (self.a, self.b)


ZERO, ONE, W = E(0), E(1), E(0, 1)
W2 = W * W


def mat(rows):
    return tuple(tuple(x if isinstance(x, E) else E(x) for x in r) for r in rows)


def mmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return tuple(tuple(sum((A[i][k] * B[k][j] for k in range(m)), ZERO) for j in range(p)) for i in range(n))


def eye(n):
    return mat([[1 if i == j else 0 for j in range(n)] for i in range(n)])


def mkey(A):
    return tuple(x.key() for r in A for x in r)


def mpow(A, k, Ainv):
    n = len(A)
    R = eye(n)
    for _ in range(abs(k)):
        R = mmul(R, A if k > 0 else Ainv)
    return R


def rank(A):
    M = [list(r) for r in A]
    rows, cols = len(M), len(M[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if not M[i][c].iszero()), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        iv = M[r][c].inv()
        M[r] = [x * iv for x in M[r]]
        for i in range(rows):
            if i != r and not M[i][c].iszero():
                f = M[i][c]
                M[i] = [M[i][j] - f * M[r][j] for j in range(cols)]
        r += 1
        if r == rows:
            break
    return r


def msub(A, B):
    return tuple(tuple(A[i][j] - B[i][j] for j in range(len(A[0]))) for i in range(len(A)))


def scal(A, s):
    n = len(A)
    return msub(A, tuple(tuple(s if i == j else ZERO for j in range(n)) for i in range(n)))


def nullity(A):
    return len(A[0]) - rank(A)


def evaluate(word, env):
    """evaluate a GAP word like (y*x^-1)^2*x^3 on matrices env = {letter: (M, Minv)}."""
    tokens = word.replace("^-1", "~").replace("*", " ")
    def ev(s, i):
        n = len(env["x"][0])
        R = eye(n)
        while i < len(s):
            ch = s[i]
            if ch == "(":
                sub, i = ev(s, i + 1)
                if i + 1 < len(s) and s[i + 1] == "^":
                    j = i + 2
                    while j < len(s) and s[j].isdigit():
                        j += 1
                    k = int(s[i + 2:j])
                    Rk = eye(n)
                    for _ in range(k):
                        Rk = mmul(Rk, sub)
                    sub = Rk
                    i = j - 1
                R = mmul(R, sub)
            elif ch == ")":
                return R, i
            elif ch in env:
                M, Minv = env[ch]
                if i + 1 < len(s) and s[i + 1] == "~":
                    R = mmul(R, Minv)
                    i += 1
                elif i + 1 < len(s) and s[i + 1] == "^":
                    j = i + 2
                    while j < len(s) and s[j].isdigit():
                        j += 1
                    R = mmul(R, mpow(M, int(s[i + 2:j]), Minv))
                    i = j - 1
                else:
                    R = mmul(R, M)
            i += 1
        return R, i
    return ev(tokens.replace(" ", ""), 0)[0]


def group_order(gens, cap):
    I = eye(len(gens[0]))
    seen = {mkey(I)}
    frontier = [I]
    while frontier and len(seen) <= cap:
        new = []
        for M in frontier:
            for g in gens:
                P = mmul(M, g)
                k = mkey(P)
                if k not in seen:
                    seen.add(k)
                    new.append(P)
        frontier = new
    return len(seen)


def refl_family():
    for k in (Fr(1, 3), Fr(2, 3)):
        S = mat([[W, 0], [0, 1]])
        Sinv = mat([[W2, 0], [0, 1]])
        u = [E(k), ONE]
        v = [ONE, E(1 - k)]
        T = tuple(tuple((ONE if i == j else ZERO) + (W - ONE) * u[i] * v[j] for j in range(2)) for i in range(2))
        Tinv = tuple(tuple((ONE if i == j else ZERO) + (W2 - ONE) * u[i] * v[j] for j in range(2)) for i in range(2))
        for es, et in itertools.product((1, -1), repeat=2):
            X = (S, Sinv) if es == 1 else (Sinv, S)
            Y = (T, Tinv) if et == 1 else (Tinv, T)
            yield "refl(k=%s, x=s^%d, y=t^%d)" % (k, es, et), X, Y


def a5_family():
    three_cycles = [p for p in itertools.permutations(range(5))
                    if sum(1 for i in range(5) if p[i] != i) == 3 and all(p[p[p[i]]] == i for i in range(5))]
    def aug(p):  # action on e_i - e_5, i = 0..3 (points 0..4, e_4 is the base point)
        M = [[0] * 4 for _ in range(4)]
        for i in range(4):
            j = p[i]
            if j < 4:
                M[j][i] += 1
            if p[4] < 4:
                M[p[4]][i] -= 1
        return mat(M)
    def pinv(p):
        q = [0] * 5
        for i, j in enumerate(p):
            q[j] = i
        return tuple(q)
    for p, q in itertools.product(three_cycles, repeat=2):
        yield "A5-augmentation(x=%s, y=%s)" % (p, q), (aug(p), aug(pinv(p))), (aug(q), aug(pinv(q)))


def wreath_family():
    P = mat([[0, 0, 1], [1, 0, 0], [0, 1, 0]])
    Pinv = mat([[0, 1, 0], [0, 0, 1], [1, 0, 0]])
    D = mat([[1, 0, 0], [0, 1, 0], [0, 0, W]])
    Dinv = mat([[1, 0, 0], [0, 1, 0], [0, 0, W2]])
    for (nx, X), (ny, Y) in itertools.product([("P", (P, Pinv)), ("P^-1", (Pinv, P)), ("D", (D, Dinv)), ("D^-1", (Dinv, D))], repeat=2):
        if {nx[0], ny[0]} == {"P", "D"}:
            yield "C3wrC3-monomial(x=%s, y=%s)" % (nx, ny), X, Y


def certify_vertex(words, order):
    for fam in (refl_family, a5_family, wreath_family):
        for name, X, Y in fam():
            env = {"x": X, "y": Y}
            n = len(X[0])
            if any(mkey(evaluate(wd, env)) != mkey(eye(n)) for wd in words):
                continue
            if group_order([X[0], Y[0]], cap=order + 1) != order:
                continue
            I = eye(n)
            fx, fy = nullity(msub(X[0], I)), nullity(msub(Y[0], I))
            # kernel bases: rank of the stacked system (X-1; Y-1) is n iff M^x and M^y meet trivially
            stacked = msub(X[0], I) + msub(Y[0], I)
            meet = n - rank(stacked)
            split = (fx + fy == n) and meet == 0
            mults = {lbl: (nullity(scal(M[0], W)), nullity(scal(M[0], W2))) for lbl, M in (("x", X), ("y", Y))}
            return dict(module=name, n=n, fx=fx, fy=fy, meet=meet, split=split, mults=mults)
    return None


def linear_characters(words):
    """linear characters lambda: B -> C3 = <w>, as exponent pairs (i, j) with lambda(x) = w^i, lambda(y) = w^j."""
    out = []
    for i, j in itertools.product(range(3), repeat=2):
        env ={"x": (mat([[[ONE, W, W2][i]]]), mat([[[ONE, W2, W][i]]])), "y": (mat([[[ONE, W, W2][j]]]), mat([[[ONE, W2, W][j]]]))}
        if all(mkey(evaluate(wd, env)) == mkey(eye(1)) for wd in words):
            out.append((i, j))
    return out


if __name__ == "__main__":
    targets = {"cckw334_q.g": ["G_0^{16,16,48}", "G_0^{16,16,54}"], "cckw334_yes.g": ["G_0^{16,16,40}", "G_1^{16,16,48}"],
               "cckw344_q.g": ["G_0^{16,40,48}"],
               "cckw444_q.g": ["G_0^{48,48,48}", "G_0^{48,54,54}", "G_8^{48,54,54}", "G_0^{54,54,54}", "G_2^{54,54,54}"]}
    cache = {}
    allok = True
    for f, names in targets.items():
        for gname, rels in parse(f):
            if gname not in names:
                continue
            dvs = []
            for pair in [("a", "b"), ("b", "c"), ("c", "a")]:
                ws = vertex_words(rels, pair)
                key = tuple(sorted(w_.replace(pair[0], "x").replace(pair[1], "y") for w_ in ws))
                if key not in cache:
                    gx, gy = vertex_group(ws, pair)
                    order = len(perm_elements([gx, gy]))
                    cert = certify_vertex(list(key), order)
                    lins = linear_characters(list(key))
                    cache[key] = (order, cert, lins)
                    print("vertex", key, "| |B| =", order, "(label %d)" % (2 * order // 3))
                    print("   module:", cert)
                    print("   linear characters (i,j) with lambda(x)=w^i, lambda(y)=w^j:", lins)
                order, cert, lins = cache[key]
                if cert is None or not cert["split"]:
                    print("   NO CERTIFIED SPLIT MODULE"); allok = False; dvs.append(None); continue
                dx, dy = 2 * (cert["n"] - cert["fx"]), 2 * (cert["n"] - cert["fy"])   # W = M + conj(M)
                extra = ""
                if dx != dy:
                    # dx > dy: add lambda with lambda(x) = 1, lambda(y) != 1 (delta(lambda) = 0; it adds to [y,W] only)
                    # dy > dx: add lambda with lambda(y) = 1, lambda(x) != 1
                    need = (1, 0) if dx > dy else (0, 1)
                    lam = [(i, j) for (i, j) in lins if (need == (1, 0) and i == 0 and j != 0) or (need == (0, 1) and j == 0 and i != 0)]
                    gap = abs(dx - dy)
                    if not lam or gap % 2:
                        print("   CANNOT BALANCE"); allok = False; dvs.append(None); continue
                    extra = " + (lambda + conj lambda)^%d, lambda = %s" % (gap // 2, lam[0])
                    dx = dy = max(dx, dy)
                dvs.append(dx)
                print("  ", gname, pair, "W_v = M + conj(M)" + extra, "| dim [x,W_v] = dim [y,W_v] =", dx)
            if None in dvs:
                continue
            d = math.lcm(*dvs)
            print("GROUP", gname, "| vertex d_v =", dvs, "| common edge module (w + w^2)^%d | dim V = %d | S1-S3 CERTIFIED" % (d // 2, 3 * d))
    print("ALL CERTIFIED" if allok else "SOME NOT CERTIFIED")
