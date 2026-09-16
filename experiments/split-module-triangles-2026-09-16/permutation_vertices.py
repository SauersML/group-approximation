#!/usr/bin/env python3
"""Corollary C of research/artifacts/split-module-triangles-of-finite-groups-2026-09-16.md (section 6b):
"two cycles sharing one point" vertex groups, and a floating-point consistency check of Theorem A with edge
groups of order 2, 3, 4, 5.

Scope.
 (a) For 2 <= p <= q with p + q - 1 <= 9: B(p,q) = <x, y> <= Sym(n), n = p + q - 1, with
     x = (0 1 ... p-1), y = (p-1 p ... n-1).  Computed exactly (permutations): |B|, whether B = Alt(n) or Sym(n),
     the orbit-graph tree test orb<x> + orb<y> = n + 1, and the half-girth r(p,q) of the coset graph of
     <x>, <y> in B (bipartite graph on the left cosets g<x>, g<y>; adjacency = nonempty intersection; BFS from the
     coset <x> is enough because B is transitive on each colour class, and every cycle meets both classes).
 (b) Theorem A numerically, for the triangles with edge orders (p_a, p_b, p_c) in {(3,3,3), (4,4,4), (3,4,5),
     (2,3,4), (5,5,5)}: vertex <a,b> = B(p_a, p_b) etc., W_v = augmentation module of C[Omega_v] (dim n_v - 1).
     Build pi_e, sigma_e(x) = 1 + J_e (rho_e(x) - 1) pi_e and sigma_v on V = U_a + U_b + U_c exactly as in
     artifact section 3, with U_e = C^{p_e - 1} (x acting by diag(zeta, ..., zeta^{p-1})), and check
       - pi_e|U_e = id,
       - sigma_v(x) = sigma_e(x) for both vertices v on the edge e (the compatibility of Step 6),
       - sigma_v(x)^{p_x} = 1 and that the orders of the matrix groups <sigma_v(x), sigma_v(y)> equal |B|
         (enumeration with entries rounded to 1e-6; only when |B| <= 5040).
     This is a floating-point consistency check, not a certificate; Theorem A is proved by hand.
Command: timeout 600 python3 -B permutation_vertices.py > permutation_vertices.out 2>&1
"""
import os
for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
import cmath, math, itertools
from collections import deque
import numpy as np


def compose(g, h):  # (g o h)(i) = g(h(i)): apply h first
    return tuple(g[h[i]] for i in range(len(h)))


def cycle_perm(n, pts):
    p = list(range(n))
    for i, a in enumerate(pts):
        p[a] = pts[(i + 1) % len(pts)]
    return tuple(p)


def generate(gens):
    n = len(gens[0])
    e = tuple(range(n))
    seen = {e}
    frontier = [e]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                h = compose(s, g)
                if h not in seen:
                    seen.add(h)
                    new.append(h)
        frontier = new
    return seen


def sign(p):
    n, seen, s = len(p), set(), 1
    for i in range(n):
        if i in seen:
            continue
        j, L = i, 0
        while j not in seen:
            seen.add(j)
            j = p[j]
            L += 1
        s *= (-1) ** (L - 1)
    return s


def orbits(gen):
    n, seen, k = len(gen), set(), 0
    for i in range(n):
        if i not in seen:
            k += 1
            j = i
            while j not in seen:
                seen.add(j)
                j = gen[j]
    return k


def half_girth(elems, x, y, p, q):
    elems = list(elems)
    idx = {g: i for i, g in enumerate(elems)}
    X = [tuple(range(len(x)))]
    for _ in range(p - 1):
        X.append(compose(X[-1], x))
    Y = [tuple(range(len(y)))]
    for _ in range(q - 1):
        Y.append(compose(Y[-1], y))
    cX = [min(idx[compose(g, e)] for e in X) for g in elems]
    cY = [min(idx[compose(g, f)] for f in Y) for g in elems]
    # neighbours of the coset gX are the cosets (g e) Y; of gY the cosets (g f) X
    root = ("X", cX[idx[X[0]]])
    dist, parent = {root: 0}, {root: None}
    dq = deque([(root, X[0])])
    best = math.inf
    while dq:
        (t, c), g = dq.popleft()
        for s in (X if t == "X" else Y):
            h = compose(g, s)
            nb = ("Y", cY[idx[h]]) if t == "X" else ("X", cX[idx[h]])
            if nb not in dist:
                dist[nb] = dist[(t, c)] + 1
                parent[nb] = (t, c)
                dq.append((nb, h))
            elif parent[(t, c)] != nb:
                best = min(best, dist[(t, c)] + dist[nb] + 1)
        if 2 * dist[(t, c)] > best:
            break
    return best // 2


def vertex_data(p, q):
    n = p + q - 1
    x = cycle_perm(n, list(range(p)))
    y = cycle_perm(n, list(range(p - 1, n)))
    elems = generate([x, y])
    N = len(elems)
    alt = all(sign(g) == 1 for g in elems)
    name = "Alt(%d)" % n if (alt and N == math.factorial(n) // 2) else ("Sym(%d)" % n if N == math.factorial(n) else "order %d" % N)
    tree = orbits(x) + orbits(y) == n + 1
    r = half_girth(elems, x, y, p, q)
    return dict(n=n, x=x, y=y, order=N, name=name, tree=tree, r=r)


def perm_matrix(g):
    n = len(g)
    M = np.zeros((n, n))
    for i in range(n):
        M[g[i], i] = 1.0
    return M


def aug_module(g):
    """matrix of g on the sum-zero subspace, basis e_i - e_{n-1}, i < n-1."""
    n = len(g)
    B = np.zeros((n, n - 1))
    for i in range(n - 1):
        B[i, i], B[n - 1, i] = 1.0, -1.0
    Binv = np.linalg.pinv(B)
    return Binv @ perm_matrix(g) @ B


def eig_blocks(M, k):
    """basis of [<x>, W] ordered by eigenvalue zeta^1, ..., zeta^{k-1} (each of multiplicity 1 here)."""
    n = M.shape[0]
    cols, mult = [], []
    for j in range(1, k):
        lam = cmath.exp(2j * cmath.pi * j / k)
        U, sv, Vh = np.linalg.svd(M - lam * np.eye(n))
        m = int(np.sum(sv < 1e-8))
        cols.append(Vh.conj().T[:, n - m:])
        mult.append(m)
    return np.hstack(cols), mult


def mat_group_order(gens, cap):
    key = lambda M: np.round(M.real * 1e6).astype(np.int64).tobytes() + np.round(M.imag * 1e6).astype(np.int64).tobytes()
    I = np.eye(gens[0].shape[0], dtype=complex)
    seen, frontier = {key(I)}, [I]
    while frontier and len(seen) <= cap:
        new = []
        for M in frontier:
            for g in gens:
                P = M @ g
                kk = key(P)
                if kk not in seen:
                    seen.add(kk)
                    new.append(P)
        frontier = new
    return len(seen)


def theorem_a_check(orders, vd):
    letters = "abc"
    po = dict(zip(letters, orders))
    pairs = [("a", "b"), ("b", "c"), ("c", "a")]
    D = {x: po[x] - 1 for x in letters}
    offs = {"a": 0, "b": D["a"], "c": D["a"] + D["b"]}
    dimV = sum(D.values())
    pi = {x: np.zeros((D[x], dimV), dtype=complex) for x in letters}
    idblock, iota, mods = {x: [] for x in letters}, {}, {}
    for (x, y) in pairs:
        d = vd[(po[x], po[y])]
        Wx, Wy = aug_module(d["x"]).astype(complex), aug_module(d["y"]).astype(complex)
        n = Wx.shape[0]
        I = np.eye(n)
        Px = sum(np.linalg.matrix_power(Wx, i) for i in range(po[x])) / po[x]
        Py = sum(np.linalg.matrix_power(Wy, i) for i in range(po[y])) / po[y]
        assert np.linalg.matrix_rank(Px, tol=1e-6) + np.linalg.matrix_rank(Py, tol=1e-6) == n, "(S2) fails"
        Bx, mx = eig_blocks(Wx, po[x])
        By, my = eig_blocks(Wy, po[y])
        assert mx == [1] * D[x] and my == [1] * D[y], (mx, my)
        Mv = np.hstack([Bx, By])           # iota_v^{-1} : U_x + U_y -> W_v
        Minv = np.linalg.inv(Mv)
        px = (Minv @ (I - Px))[:D[x], :] @ Mv
        py = (Minv @ (I - Py))[D[x]:, :] @ Mv
        pi[x][:, offs[x]:offs[x] + D[x]] = px[:, :D[x]]
        pi[x][:, offs[y]:offs[y] + D[y]] = px[:, D[x]:]
        pi[y][:, offs[x]:offs[x] + D[x]] = py[:, :D[x]]
        pi[y][:, offs[y]:offs[y] + D[y]] = py[:, D[x]:]
        idblock[x].append(np.abs(px[:, :D[x]] - np.eye(D[x])).max())
        idblock[y].append(np.abs(py[:, D[x]:] - np.eye(D[y])).max())
        mods[(x, y)] = (Mv, Minv, Wx, Wy)
    sig_e = {}
    for x in letters:
        rho = np.diag([cmath.exp(2j * cmath.pi * j / po[x]) for j in range(1, po[x])])
        J = np.zeros((dimV, D[x]))
        J[offs[x]:offs[x] + D[x], :] = np.eye(D[x])
        sig_e[x] = np.eye(dimV) + J @ (rho - np.eye(D[x])) @ pi[x]
    comp_err, pow_err, orders_ok = 0.0, 0.0, []
    for (x, y) in pairs:
        Mv, Minv, Wx, Wy = mods[(x, y)]
        # V = (U_x + U_y) + K_v, K_v = ker pi_x cap ker pi_y
        Pxy = np.vstack([pi[x], pi[y]])
        U, sv, Vh = np.linalg.svd(Pxy)
        K = Vh.conj().T[:, Pxy.shape[0]:]
        Qb = np.zeros((dimV, D[x] + D[y]), dtype=complex)
        Qb[offs[x]:offs[x] + D[x], :D[x]] = np.eye(D[x])
        Qb[offs[y]:offs[y] + D[y], D[x]:] = np.eye(D[y])
        Q = np.hstack([Qb, K])
        Qinv = np.linalg.inv(Q)
        def sig_v(Wa):
            blk = np.eye(dimV, dtype=complex)
            m = D[x] + D[y]
            blk[:m, :m] = Minv @ Wa @ Mv
            return Q @ blk @ Qinv
        Sx, Sy = sig_v(Wx), sig_v(Wy)
        comp_err = max(comp_err, np.abs(Sx - sig_e[x]).max(), np.abs(Sy - sig_e[y]).max())
        pow_err = max(pow_err, np.abs(np.linalg.matrix_power(sig_e[x], po[x]) - np.eye(dimV)).max())
        N = vd[(po[x], po[y])]["order"]
        if N <= 5040:
            orders_ok.append(mat_group_order([sig_e[x], sig_e[y]], cap=N + 1) == N)
    idb = max(max(v) for v in idblock.values())
    ok = comp_err < 1e-7 and pow_err < 1e-7 and idb < 1e-8 and all(orders_ok)
    print("edge orders", orders, "| dim V =", dimV, "| pi_e|U_e = id err %.1e" % idb,
          "| max ||sigma_v(x) - sigma_e(x)|| = %.1e" % comp_err, "| sigma_e(x)^p = 1 err %.1e" % pow_err,
          "| <sigma_e(x), sigma_e(y)> has order |B| (checked where |B| <= 5040):", orders_ok, "| OK" if ok else "| FAIL")
    return ok


if __name__ == "__main__":
    vd = {}
    print("(a) vertex groups B(p,q) = <(0..p-1), (p-1..p+q-2)>")
    for p in range(2, 6):
        for q in range(p, 9):
            if p + q - 1 > 9 or (p, q) == (2, 2) and False:
                continue
            d = vertex_data(p, q)
            vd[(p, q)] = d
            vd[(q, p)] = dict(d, x=cycle_perm(d["n"], list(range(q))), y=cycle_perm(d["n"], list(range(q - 1, d["n"]))))
            print("  p=%d q=%d | n=%d | |B|=%d (%s) | orbit graph tree: %s | half-girth r = %s" % (p, q, d["n"], d["order"], d["name"], d["tree"], d["r"]))
    print("(b) Theorem A with W_v = augmentation module, floating point")
    allok = True
    for orders in [(3, 3, 3), (4, 4, 4), (3, 4, 5), (2, 3, 4), (5, 5, 5)]:
        allok &= theorem_a_check(orders, vd)
    print("ALL OK" if allok else "SOME FAIL")
