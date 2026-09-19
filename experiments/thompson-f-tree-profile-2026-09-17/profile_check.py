"""Checks for thompson-f-near-eigenvectors-have-fibonacci-tree-profiles.

Model (thompson-f-one-sided-forest-windows-are-norm-lossless, item 3): a vertex of Gamma_R is a
one-sided pointed forest (T_0, T_1, ...; i), finitely many nontrivial trees, pointer i >= 0.
Moves: R (pointer right, a bijection onto {i >= 1}) and M (merge T_i with T_{i+1}, a bijection onto
{T_i not a leaf}).  For unit f >= 0 put Q = f^2, t_R = TV(Q, R_*Q), t_M = TV(Q, M_*Q),
BC_R = <f, f o R^{-1}>, BC_M likewise, eta = 1 - <f, K f>/4 = (2 - BC_R - BC_M)/2 (compression form).

Part A: brute force of the run lemma on all integer sequences.
Part B: for Perron vectors of the move graph on the windows W_n (all nontrivial trees and the pointer
among the first n leaves) and for random perturbations, check
    Q(bad_0) <= 2 t_M + 3 t_R,     t_M + t_R <= 2 sqrt(2) sqrt(eta),
    Q(bad_j) <= Q(bad_0) + |j| t_R.
Prints OK lines.
"""
import itertools, math, random
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh

LEAF = 0  # a leaf; a caret is a pair (L, R)


def size(t):
    return 1 if t == LEAF else size(t[0]) + size(t[1])


def canon(trees, i):
    trees = list(trees)
    while len(trees) > i + 1 and trees[-1] == LEAF:
        trees.pop()
    while len(trees) < i + 1:
        trees.append(LEAF)
    return (tuple(trees), i)


def tree_at(trees, k):
    return trees[k] if k < len(trees) else LEAF


def move_R(v):
    trees, i = v
    return canon(trees, i + 1)


def move_M(v):
    trees, i = v
    tr = list(trees) + [LEAF]
    new = tr[:i] + [(tr[i], tr[i + 1])] + tr[i + 2:]
    return canon(new, i)


def sizes(v, j):
    trees, i = v
    k = i + j
    return None if k < 0 else size(tree_at(trees, k))


def bad(v, j):
    """bad_j: pointer+j <= 0, or C1_j, or C2_j (weak local minima lie in C1 u C2)."""
    trees, i = v
    if i + j <= 0:
        return True
    a, b, c = sizes(v, j - 1), sizes(v, j), sizes(v, j + 1)
    c1 = (b <= c < a + b)
    c2 = (b <= a < b + c)
    return c1 or c2


# ---------------------------------------------------------------- Part A
def fib(k):
    a, b = 1, 1
    for _ in range(k - 1):
        a, b = b, a + b
    return a  # F_1 = F_2 = 1


def partA(Kmax=6):
    """DFS over all sequences x_0..x_{2K} in [1,B] with no C1/C2 at interior positions.
    With B = F_(K+2) - 1 there must be none; with B = F_(K+2) the bound is attained."""
    for K, B in [(k, fib(k + 2) + e) for k in range(2, Kmax + 1) for e in (-1, 0)]:
        L = 2 * K + 1
        worst = [None]
        count = [0]

        def dfs(x):
            n = len(x)
            if n >= 3:
                a, b, c = x[-3], x[-2], x[-1]
                if (b <= c < a + b) or (b <= a < b + c):
                    return
            if n == L:
                count[0] += 1
                m = max(x)
                if worst[0] is None or m < worst[0]:
                    worst[0] = m
                assert m >= fib(K + 2), (x, K)
                return
            for v in range(1, B + 1):
                x.append(v)
                dfs(x)
                x.pop()

        dfs([])
        print(f"OK A K={K} B={B}: {count[0]} good windows of length {L} with entries <= {B}; "
              f"min of max = {worst[0]} >= F_(K+2) = {fib(K+2)}")


# ---------------------------------------------------------------- Part B
def trees_with(n):
    if n == 1:
        return [LEAF]
    out = []
    for k in range(1, n):
        for l in trees_with(k):
            for r in trees_with(n - k):
                out.append((l, r))
    return out


def forests(n):
    """compositions of n leaves into trees."""
    if n == 0:
        yield ()
        return
    for k in range(1, n + 1):
        for t in trees_with(k):
            for rest in forests(n - k):
                yield (t,) + rest


def window(n):
    V = set()
    for fo in forests(n):
        for i in range(len(fo)):
            V.add(canon(fo, i))
    return sorted(V, key=repr)


def stats(V, f):
    idx = {v: k for k, v in enumerate(V)}
    Q = {v: f[idx[v]] ** 2 for v in V}
    out = {}
    for name, mv in (("R", move_R), ("M", move_M)):
        push = {}
        for v, q in Q.items():
            w = mv(v)
            push[w] = push.get(w, 0.0) + q
        keys = set(Q) | set(push)
        out["t" + name] = 0.5 * sum(abs(Q.get(k, 0) - push.get(k, 0)) for k in keys)
        out["BC" + name] = sum(math.sqrt(Q.get(k, 0) * push.get(k, 0)) for k in keys)
    out["eta"] = (2 - out["BCR"] - out["BCM"]) / 2
    out["bad"] = {j: sum(q for v, q in Q.items() if bad(v, j)) for j in range(-3, 4)}
    return out


def perron(V):
    idx = {v: k for k, v in enumerate(V)}
    rows, cols = [], []
    for v in V:
        for mv in (move_R, move_M):
            w = mv(v)
            if w in idx:
                rows += [idx[v], idx[w]]
                cols += [idx[w], idx[v]]
    A = coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(V), len(V))).tocsr()
    val, vec = eigsh(A, k=1, which="LA")
    f = np.abs(vec[:, 0])
    return val[0], f / np.linalg.norm(f)


def check(V, f, label):
    s = stats(V, f)
    tR, tM, eta = s["tR"], s["tM"], s["eta"]
    b0 = s["bad"][0]
    assert b0 <= 2 * tM + 3 * tR + 1e-12
    assert tM + tR <= 2 * math.sqrt(2) * math.sqrt(max(eta, 0)) + 1e-12
    for j, bj in s["bad"].items():
        assert bj <= b0 + abs(j) * tR + 1e-12, (j, bj, b0, tR)
    return s


def partB(nmax=8, trials=20):
    rng = random.Random(1)
    for n in range(4, nmax + 1):
        V = window(n)
        lam, f = perron(V)
        s = check(V, f, "perron")
        print(f"OK B n={n} |W|={len(V)} rho/4={lam/4:.4f} eta={s['eta']:.4f} "
              f"Q(bad0)={s['bad'][0]:.4f} <= 2tM+3tR={2*s['tM']+3*s['tR']:.4f}")
        for _ in range(trials):
            g = np.array([x * math.exp(rng.gauss(0, 0.5)) for x in f])
            g /= np.linalg.norm(g)
            check(V, g, "pert")
        print(f"OK B n={n}: {trials} random perturbations satisfy all three inequalities")


if __name__ == "__main__":
    partA()
    partB()
