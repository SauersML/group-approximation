"""Cross-checks for upper-triangular-cloning-group-contains-lamplighter-over-z2.

1. Witzel-Zaremsky cloning on B_n(F_p) (arXiv:1405.5491, Sec. 7): homomorphism, (C2), compatibility (2).
2. A small implementation of T(B_*(F_p)) (pure case, rho trivial): expansions, products, equality.
3. Root-split unipotent blocks [[I,X],[0,I]] stay in block form under expansion, and the invariant
   Phi(T, X) = sum_ij X_ij delta_{b_i} (x) (1_[c_j,1) - 1_[d_j,1)) does not change.
4. With g in F_L, h in F_R and the lamp a, the relations of F_p wr Z^2 hold on a window, and the
   translates a^(g^i h^j) have Phi = +-delta_{x_i} (x) 1_[y_j,1) with pairwise distinct (x_i, y_j).
"""
from fractions import Fraction as Fr
import itertools
import random

random.seed(1)
P = 3  # the field F_p


def kappa(A, k):
    """Clone row/column k (1-indexed). ((A)kappa_k)_ij = A_{pi(i) pi(j)} unless i = k or i > j."""
    n = len(A)
    pi = lambda i: i if i <= k else i - 1
    B = [[0] * (n + 1) for _ in range(n + 1)]
    for i in range(1, n + 2):
        for j in range(1, n + 2):
            if i > j:
                continue
            if i == k and j != k:
                continue
            B[i - 1][j - 1] = A[pi(i) - 1][pi(j) - 1]
    return B


def mul(A, B):
    n = len(A)
    return [[sum(A[i][t] * B[t][j] for t in range(n)) % P for j in range(n)] for i in range(n)]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def rand_b(n):
    return [[(random.randrange(1, P) if i == j else random.randrange(P)) if i <= j else 0
             for j in range(n)] for i in range(n)]


def iota(A, n):
    m = len(A)
    B = eye(n)
    for i in range(m):
        for j in range(m):
            B[i][j] = A[i][j]
    return B


def check_axioms():
    # Figure 6 of WZ
    assert kappa([[1, 2, 3], [0, 4, 5], [0, 0, 6]], 2) == [[1, 2, 2, 3], [0, 4, 0, 0], [0, 0, 4, 5], [0, 0, 0, 6]]
    for n in range(1, 6):
        for _ in range(40):
            A, B = rand_b(n), rand_b(n)
            for k in range(1, n + 1):
                assert kappa(mul(A, B), k) == mul(kappa(A, k), kappa(B, k)), "C1"
            for k in range(1, n + 1):
                for l in range(k, n + 1):  # C2 for k < l, and also l = k (WZ remark)
                    assert kappa(kappa(A, l), k) == kappa(kappa(A, k), l + 1), "C2"
            for m in range(n, n + 3):
                for k in range(1, n + 1):
                    assert kappa(iota(A, m), k) == iota(kappa(A, k), m + 1), "(2)"
    print("cloning axioms on B_n(F_%d), n <= 5: ok" % P)


# ---- trees as sorted lists of dyadic intervals (a, b) ----

def split(tree, k):
    a, b = tree[k]
    m = (a + b) / 2
    return tree[:k] + [(a, m), (m, b)] + tree[k + 1:]


def expand(el, k):
    tm, M, tp = el
    return (split(tm, k), kappa(M, k + 1), split(tp, k))


def refine_plus_to(el, S):
    """Expand el so that its T_+ equals the refinement S of T_+."""
    while el[2] != S:
        tp = el[2]
        for k, (a, b) in enumerate(tp):
            if (a, b) not in S:
                el = expand(el, k)
                break
    return el


def refine_minus_to(el, S):
    while el[0] != S:
        tm = el[0]
        for k, (a, b) in enumerate(tm):
            if (a, b) not in S:
                el = expand(el, k)
                break
    return el


def union(T1, T2):
    pts = sorted(set([a for a, _ in T1] + [a for a, _ in T2] + [Fr(1)]))
    # union of two dyadic subdivisions is again a tree subdivision
    return [(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]


def prod(x, y):
    S = union(x[2], y[0])
    x2 = refine_plus_to(x, S)
    y2 = refine_minus_to(y, S)
    return (x2[0], mul(x2[1], y2[1]), y2[2])


def inv(x):
    tm, M, tp = x
    n = len(M)
    # inverse of an upper triangular matrix over F_p, by brute force solve
    Minv = eye(n)
    A = [row[:] for row in M]
    for i in reversed(range(n)):
        d = pow(A[i][i], P - 2, P)
        for j in range(n):
            A[i][j] = A[i][j] * d % P
            Minv[i][j] = Minv[i][j] * d % P
        for r in range(i):
            f = A[r][i]
            for j in range(n):
                A[r][j] = (A[r][j] - f * A[i][j]) % P
                Minv[r][j] = (Minv[r][j] - f * Minv[i][j]) % P
    return (tp, Minv, tm)


def equal(x, y):
    """Expand both to a common pair of trees; pure case, so splits are simultaneous."""
    for _ in range(200):
        if x[0] == y[0] and x[2] == y[2]:
            return x[1] == y[1]
        moved = False
        for k, iv in enumerate(x[0]):
            if iv not in y[0]:
                x = expand(x, k); moved = True; break
        if moved:
            continue
        for k, iv in enumerate(y[0]):
            if iv not in x[0]:
                y = expand(y, k); moved = True; break
        if not moved:
            return False  # same T_-, different T_+: different F-parts
    raise RuntimeError("no convergence")


def is_identity(x):
    return x[0] == x[2] and x[1] == eye(len(x[1]))


def phi(el):
    """Return Phi of a pure root-split unipotent block element, or None if not of that form."""
    tm, M, tp = el
    if tm != tp:
        return None
    m = sum(1 for (a, b) in tp if b <= Fr(1, 2))
    n = len(M)
    for i in range(n):
        for j in range(n):
            want = int(i == j)
            if not (i < m and j >= m) and M[i][j] % P != want:
                return None
    out = {}
    for i in range(m):
        bi = tp[i][1]
        for j in range(m, n):
            cj, dj = tp[j]
            v = M[i][j] % P
            if v:
                out[(bi, cj)] = (out.get((bi, cj), 0) + v) % P
                if dj != 1:
                    out[(bi, dj)] = (out.get((bi, dj), 0) - v) % P
    return {key: v for key, v in out.items() if v}


def dy(*s):
    return [(Fr(a), Fr(b)) for a, b in s]


def check_phi_invariance():
    # random root-split trees, random blocks, random expansions
    count = 0
    for _ in range(60):
        T = dy((0, Fr(1, 2)), (Fr(1, 2), 1))
        for _ in range(random.randrange(0, 5)):
            T = split(T, random.randrange(len(T)))
        n = len(T)
        m = sum(1 for (a, b) in T if b <= Fr(1, 2))
        M = eye(n)
        for i in range(m):
            for j in range(m, n):
                M[i][j] = random.randrange(P)
        el = (T, M, T)
        base = phi(el)
        assert base is not None
        for _ in range(6):
            el = expand(el, random.randrange(len(el[0])))
            assert phi(el) == base, "Phi not invariant / block form lost"
            count += 1
    print("block form and Phi invariant under %d random expansions: ok" % count)


def power(x, e):
    n = len(x[1])
    if e < 0:
        x, e = inv(x), -e
    r = (x[0], eye(n), x[0])
    for _ in range(e):
        r = prod(r, x)
    return r


def conj(a, w):
    return prod(prod(inv(w), a), w)


def check_lamplighter(W=3):
    half = Fr(1, 2)
    g = (dy((0, Fr(1, 8)), (Fr(1, 8), Fr(1, 4)), (Fr(1, 4), half), (half, 1)), eye(4),
         dy((0, Fr(1, 4)), (Fr(1, 4), Fr(3, 8)), (Fr(3, 8), half), (half, 1)))
    h = (dy((0, half), (half, Fr(5, 8)), (Fr(5, 8), Fr(3, 4)), (Fr(3, 4), 1)), eye(4),
         dy((0, half), (half, Fr(3, 4)), (Fr(3, 4), Fr(7, 8)), (Fr(7, 8), 1)))
    T = dy((0, Fr(1, 4)), (Fr(1, 4), half), (half, Fr(3, 4)), (Fr(3, 4), 1))
    X = eye(4); X[0][3] = 1
    a = (T, X, T)
    assert phi(a) == {(Fr(1, 4), Fr(3, 4)): 1}
    assert equal(prod(g, h), prod(h, g)), "[g,h] != 1"
    assert is_identity(power(a, P)) or equal(power(a, P), (T, eye(4), T)), "a^p != 1"
    lamps = {}
    for i, j in itertools.product(range(-W, W + 1), repeat=2):
        w = prod(power(g, i), power(h, j))
        c = conj(a, w)
        ph = phi(c)
        if ph is None:  # expand to a common tree first; conj result has T_- = T_+ only up to expansion
            raise AssertionError("conjugate not visibly pure block at (%d,%d): %s" % (i, j, c[0]))
        assert len(ph) == 1 and list(ph.values())[0] == 1, ph
        lamps[(i, j)] = list(ph.keys())[0]
    pts = list(lamps.values())
    assert len(set(pts)) == len(pts), "translates not distinct"
    xs = {i: lamps[(i, 0)][0] for i in range(-W, W + 1)}
    ys = {j: lamps[(0, j)][1] for j in range(-W, W + 1)}
    for (i, j), (x, y) in lamps.items():
        assert x == xs[i] and y == ys[j], "not a product orbit"
    keys = list(lamps)
    for u in keys[::5]:
        for v in keys[::3]:
            cu = conj(a, prod(power(g, u[0]), power(h, u[1])))
            cv = conj(a, prod(power(g, v[0]), power(h, v[1])))
            assert equal(prod(cu, cv), prod(cv, cu)), "lamps do not commute"
    print("x-orbit:", [str(xs[i]) for i in sorted(xs)])
    print("y-orbit:", [str(ys[j]) for j in sorted(ys)])
    print("F_%d wr Z^2 relations and free product orbit on window |i|,|j| <= %d: ok" % (P, W))


if __name__ == "__main__":
    check_axioms()
    check_phi_invariance()
    check_lamplighter()
