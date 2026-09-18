"""Cubic linearization of weak-isomorphism determinant violations: verification.

Construction (see research/weak-determinant-violations-move-to-cubic-operators-proof.md):

  T in M_n(Z[K])  --(Schur trees)-->  L = [[0,E],[F,-1+K_nil]]      det L  = det T
                  --(sign removal)-> M1 = [[P,N],[1,1]]              det M1 = det L
                  --(pad deficits)-> M' = [[M1,E'],[F',G_all]]       det M' = det M1
                  over K x Z, with one gadget per deficit pair
                    G(s) = [[0,1,s],[1,1,1],[s,1,1]],  det G = -(1-s)^2,  adj(G)_{00} = 0
  M' has coefficients in N[K x Z], every row and column has coefficient sum 3,
  and M' = u1+u2+u3 with monomial unitaries (Koenig), so det M' = det(1 + w1 + w2).
  B = [[0,M'],[M'^*,0]] is cubic without inversions and det B = (det M')^2.

K = H x Z is realised with H a finite group (Z/m or S_3) and the Z coordinate kept as
a polynomial variable z. Checks:
  (1) exact: det rho(M'(z)) = +- det rho(T(z)) * (-(1-z)^2)^(g|H|)  mod p at random z,
      where rho is the regular representation of H; hence, by Mahler(1-z) = 0,
      det_{N(H x Z)} M' = det_{N(H x Z)} T;
  (2) structure: nonnegative coefficients, exact 3-regularity, B self-adjoint, zero diagonal;
  (3) Koenig: M' = u1+u2+u3 monomial, |det(1+w1+w2)| = |det M'| on |z| = 1;
  (4) negative controls: a gadget with adj(G)_{00} != 0 breaks (1); a scalar gadget cannot
      exist (gadget_search.py); non-injective T breaks the identity for det';
  (5) Theorem C(3) without the norm hypothesis: on finite 3-regular graphs (norm exactly 3,
      atoms at +-3) the violation-transfer identity for Q_m = ((t^2-9) t^m) o p_L holds.
"""
import itertools
import random
import sys

import numpy as np

P_MOD = 2147483647  # 2^31 - 1

# ---------------------------------------------------------------- groups


def cyclic(m):
    mul = [[(a + b) % m for b in range(m)] for a in range(m)]
    inv = [(-a) % m for a in range(m)]
    return {"name": f"Z/{m}", "n": m, "mul": mul, "inv": inv}


def s3():
    perms = list(itertools.permutations(range(3)))
    idx = {p: i for i, p in enumerate(perms)}
    e = idx[(0, 1, 2)]
    # reorder so identity is 0
    order = [e] + [i for i in range(6) if i != e]
    perms = [perms[i] for i in order]
    idx = {p: i for i, p in enumerate(perms)}
    mul = [[idx[tuple(p[q[k]] for k in range(3))] for q in perms] for p in perms]
    inv = [idx[tuple(sorted(range(3), key=lambda k: p[k]))] for p in perms]
    return {"name": "S_3", "n": 6, "mul": mul, "inv": inv}


# ---------------------------------------------------------------- matrices over Z[H x Z]
# element = (h, j) meaning h * s^j ; matrix = dict (row, col) -> dict element -> coeff


def madd(A, i, j, elem, c):
    if c == 0:
        return
    d = A.setdefault((i, j), {})
    d[elem] = d.get(elem, 0) + c
    if d[elem] == 0:
        del d[elem]
        if not d:
            del A[(i, j)]


def rho_complex(A, N, H, z):
    m = H["n"]
    R = np.zeros((N * m, N * m), dtype=complex)
    for (i, j), d in A.items():
        for (h, k), c in d.items():
            zk = z ** k
            for x in range(m):
                R[i * m + x, j * m + H["mul"][x][h]] += c * zk
    return R


def rho_mod(A, N, H, z):
    m = H["n"]
    R = np.zeros((N * m, N * m), dtype=np.int64)
    for (i, j), d in A.items():
        for (h, k), c in d.items():
            zk = pow(z, k, P_MOD)
            v = (c * zk) % P_MOD
            for x in range(m):
                a, b = i * m + x, j * m + H["mul"][x][h]
                R[a, b] = (R[a, b] + v) % P_MOD
    return R


def det_mod(R):
    R = R.copy() % P_MOD
    n = R.shape[0]
    det = 1
    for col in range(n):
        piv = None
        nz = np.nonzero(R[col:, col])[0]
        if len(nz) == 0:
            return 0
        piv = col + nz[0]
        if piv != col:
            R[[col, piv]] = R[[piv, col]]
            det = (-det) % P_MOD
        pv = int(R[col, col])
        det = (det * pv) % P_MOD
        invp = pow(pv, P_MOD - 2, P_MOD)
        rows = col + 1 + np.nonzero(R[col + 1:, col])[0]
        if len(rows):
            f = (R[rows, col] * invp) % P_MOD
            # R[rows] -= f * R[col]  (mod p), avoid overflow: split f into 16-bit halves
            lo = f & 0xFFFF
            hi = f >> 16
            rc = R[col]
            t = (hi[:, None] * rc[None, :]) % P_MOD
            t = (t * 65536) % P_MOD
            t = (t + lo[:, None] * rc[None, :]) % P_MOD
            R[rows] = (R[rows] - t) % P_MOD
    return det


# ---------------------------------------------------------------- construction


def random_T(n, H, rng, max_terms=3, zpow=1):
    T = {}
    for i in range(n):
        for j in range(n):
            for _ in range(rng.randint(1, max_terms)):
                h = rng.randrange(H["n"])
                k = rng.randint(-zpow, zpow)
                madd(T, i, j, (h, k), rng.choice([-1, 1]))
    return T


def linearize(T, n):
    """Return (L, NL): L = [[0,E],[F,-1+K]] with -E(-1+K)^-1 F = T."""
    monos = []
    for (i, k), d in sorted(T.items()):
        for elem, c in sorted(d.items()):
            for _ in range(abs(c)):
                monos.append((i, k, 1 if c > 0 else -1, elem))
    for i in range(n):
        assert any(m[0] == i for m in monos), "zero row"
        assert any(m[1] == i for m in monos), "zero column"
    L = {}
    counter = [n]
    E0 = (0, 0)

    def new():
        counter[0] += 1
        return counter[0] - 1

    def out_tree(cnt):
        v = new()
        if cnt == 1:
            return v, [v]
        a, la = out_tree((cnt + 1) // 2)
        b, lb = out_tree(cnt // 2)
        madd(L, v, a, E0, 1)
        madd(L, v, b, E0, 1)
        return v, la + lb

    def in_tree(cnt):
        v = new()
        if cnt == 1:
            return v, [v]
        a, la = in_tree((cnt + 1) // 2)
        b, lb = in_tree(cnt // 2)
        madd(L, a, v, E0, 1)
        madd(L, b, v, E0, 1)
        return v, la + lb

    out_leaf = {}
    for i in range(n):
        ms = [t for t, m in enumerate(monos) if m[0] == i]
        root, leaves = out_tree(len(ms))
        madd(L, i, root, E0, 1)  # E
        for t, lf in zip(ms, leaves):
            out_leaf[t] = lf
    in_leaf = {}
    for k in range(n):
        ms = [t for t, m in enumerate(monos) if m[1] == k]
        root, leaves = in_tree(len(ms))
        madd(L, root, k, E0, 1)  # F
        for t, lf in zip(ms, leaves):
            in_leaf[t] = lf
    for t, (i, k, sg, elem) in enumerate(monos):
        madd(L, out_leaf[t], in_leaf[t], elem, sg)
    NL = counter[0]
    for v in range(n, NL):
        madd(L, v, v, E0, -1)
    return L, NL


def remove_signs(L, NL):
    M = {}
    for (i, j), d in L.items():
        for elem, c in d.items():
            assert abs(c) == 1 and len(d) == 1, "L entries must be single signed monomials"
            if c > 0:
                madd(M, i, j, elem, 1)  # P
            else:
                madd(M, i, NL + j, elem, 1)  # N
    for i in range(NL):
        madd(M, NL + i, i, (0, 0), 1)
        madd(M, NL + i, NL + i, (0, 0), 1)
    return M, 2 * NL


def sums(M, N):
    rs = [0] * N
    cs = [0] * N
    for (i, j), d in M.items():
        for c in d.values():
            assert c > 0
            rs[i] += c
            cs[j] += c
    return rs, cs


GADGET = [[[(0, 0)], [(0, 0)], [(0, 1)]],
          [[(0, 0)], [(0, 0)], [(0, 0)]],
          [[(0, 1)], [(0, 0)], [(0, 0)]]]
# G(s) = [[0,1,s],[1,1,1],[s,1,1]] ; entry (0,0) is 0 (empty list in cell 0,0 replaced below)
GADGET[0][0] = []

BAD_GADGET = [[[], [(0, 0)], [(0, 1)]],
              [[(0, 0)], [(0, 0)], [(0, 1)]],
              [[(0, 1)], [(0, 0)], [(0, 0)]]]
# det = -(1-s)^2 as well? not needed: adj_{00} = 1 - s != 0 breaks E adj(G) F = 0


def pad(M, N, gadget=GADGET):
    rs, cs = sums(M, N)
    assert all(r <= 3 for r in rs) and all(c <= 3 for c in cs), (max(rs), max(cs))
    row_units = [i for i in range(N) for _ in range(3 - rs[i])]
    col_units = [j for j in range(N) for _ in range(3 - cs[j])]
    assert len(row_units) == len(col_units)
    Mp = {k: dict(v) for k, v in M.items()}
    base = N
    for a, b in zip(row_units, col_units):
        for r in range(3):
            for c in range(3):
                for elem in gadget[r][c]:
                    madd(Mp, base + r, base + c, elem, 1)
        madd(Mp, a, base + 0, (0, 0), 1)  # E': row a -> gadget column 0
        madd(Mp, base + 0, b, (0, 0), 1)  # F': gadget row 0 -> column b
        base += 3
    return Mp, base, len(row_units)


def adjoint(M, H):
    A = {}
    for (i, j), d in M.items():
        for (h, k), c in d.items():
            madd(A, j, i, (H["inv"][h], -k), c)
    return A


def bipartite_double(M, N, H):
    B = {}
    for (i, j), d in M.items():
        for elem, c in d.items():
            madd(B, i, N + j, elem, c)
    for (i, j), d in adjoint(M, H).items():
        for elem, c in d.items():
            madd(B, N + i, j, elem, c)
    return B, 2 * N


def koenig(M, N):
    """Split M (coefficients in N[H x Z], row/col sums 3) into 3 monomial matrices."""
    labels = {}
    for (i, j), d in M.items():
        for elem, c in d.items():
            labels.setdefault((i, j), []).extend([elem] * c)
    parts = []
    for rnd in range(3):
        adj = [[] for _ in range(N)]
        for (i, j), lst in labels.items():
            if lst:
                adj[i].append(j)
        match_col = [-1] * N
        sys.setrecursionlimit(100000)

        def try_row(u, seen):
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = True
                    if match_col[v] == -1 or try_row(match_col[v], seen):
                        match_col[v] = u
                        return True
            return False

        for u in range(N):
            assert try_row(u, [False] * N), "no perfect matching"
        U = {}
        for v in range(N):
            u = match_col[v]
            elem = labels[(u, v)].pop()
            madd(U, u, v, elem, 1)
        parts.append(U)
    assert all(not lst for lst in labels.values())
    return parts


def mat_mul(A, B, H):
    C = {}
    byrow = {}
    for (k, j), d in B.items():
        byrow.setdefault(k, []).append((j, d))
    for (i, k), d1 in A.items():
        for j, d2 in byrow.get(k, []):
            for (h1, k1), c1 in d1.items():
                for (h2, k2), c2 in d2.items():
                    madd(C, i, j, (H["mul"][h1][h2], k1 + k2), c1 * c2)
    return C


def mat_sum(*As):
    C = {}
    for A in As:
        for (i, j), d in A.items():
            for elem, c in d.items():
                madd(C, i, j, elem, c)
    return C


def identity(N):
    I = {}
    for i in range(N):
        madd(I, i, i, (0, 0), 1)
    return I


# ---------------------------------------------------------------- Theorem C(3) check


def finite_graph(B, N, H, q):
    """Finite 3-regular multigraph: quotient H x Z -> H x Z/q, as integer adjacency matrix."""
    m = H["n"]
    V = N * m * q
    A = np.zeros((V, V))
    for (i, j), d in B.items():
        for (h, k), c in d.items():
            for x in range(m):
                for y in range(q):
                    A[(i * m + x) * q + y, (j * m + H["mul"][x][h]) * q + (y + k) % q] += c
    return A


def subdivide(A, L):
    V = A.shape[0]
    edges = []
    for u in range(V):
        for v in range(u + 1, V):
            edges.extend([(u, v)] * int(round(A[u, v])))
        assert A[u, u] == 0
    W = V + len(edges) * (L - 1)
    S = np.zeros((W, W))
    nxt = V
    for (u, v) in edges:
        path = [u] + list(range(nxt, nxt + L - 1)) + [v]
        nxt += L - 1
        for a, b in zip(path, path[1:]):
            S[a, b] += 1
            S[b, a] += 1
    return S


def cheb_pL(L):
    U = [np.poly1d([1.0]), np.poly1d([1.0, 0.0])]
    for _ in range(L):
        U.append(np.poly1d([1.0, 0.0]) * U[-1] - U[-2])
    return np.poly1d([1.0, 0.0]) * U[L - 1] - 3 * U[L - 2]


def theorem_c3_check(A, L, mexp, tol=1e-7):
    ev_B = np.linalg.eigvalsh(A)
    ev_AL = np.linalg.eigvalsh(subdivide(A, L))
    pL = cheb_pL(L)
    R = lambda t: t ** mexp * (t * t - 9)
    lhs_vals = R(pL(ev_AL))
    lhs = sum(np.log(abs(v)) for v in lhs_vals if abs(v) > tol)
    rhs_vals = R(ev_B)
    rhs = L * sum(np.log(abs(v)) for v in rhs_vals if abs(v) > tol)
    atoms3 = int(np.sum(abs(abs(ev_B) - 3) < 1e-8))
    return lhs, rhs, atoms3, float(max(abs(ev_B)))


# ---------------------------------------------------------------- main


def run_identity(H, n, rng, zpow=1, max_terms=3, gadget=GADGET, trials_z=3):
    while True:
        T = random_T(n, H, rng, max_terms=max_terms, zpow=zpow)
        if abs(np.linalg.det(rho_complex(T, n, H, 0.37 + 0.81j))) > 1e-6:
            break
    L, NL = linearize(T, n)
    # Schur check: -E G^-1 F = T at a complex point
    z0 = 0.6 - 0.45j
    RL = rho_complex(L, NL, H, z0)
    m = H["n"]
    E = RL[: n * m, n * m:]
    F = RL[n * m:, : n * m]
    G = RL[n * m:, n * m:]
    schur_err = np.abs(-E @ np.linalg.solve(G, F) - rho_complex(T, n, H, z0)).max()
    M1, N1 = remove_signs(L, NL)
    Mp, Np, g = pad(M1, N1, gadget=gadget)
    rs, cs = sums(Mp, Np)
    regular = all(r == 3 for r in rs) and all(c == 3 for c in cs)
    ok_modp = True
    for _ in range(trials_z):
        z = rng.randrange(2, P_MOD - 1)
        dT = det_mod(rho_mod(T, n, H, z))
        dM = det_mod(rho_mod(Mp, Np, H, z))
        factor = pow((-(1 - z) ** 2) % P_MOD, g * m, P_MOD)
        target = (dT * factor) % P_MOD
        if dM not in (target, (-target) % P_MOD):
            ok_modp = False
    return dict(T=T, L=L, NL=NL, M1=M1, N1=N1, Mp=Mp, Np=Np, g=g, schur_err=schur_err,
                regular=regular, ok_modp=ok_modp)


def main():
    rng = random.Random(20260917)
    print("== (1)-(2) linearization identity and exact 3-regularity over H x Z ==")
    for H in (cyclic(2), cyclic(3), cyclic(5), s3()):
        for n in (1, 2):
            for trial in range(2):
                r = run_identity(H, n, rng)
                print(f"H={H['name']:4s} n={n} trial={trial}: size L={r['NL']:3d} M1={r['N1']:3d} "
                      f"M'={r['Np']:4d} gadgets={r['g']:3d}  schur_err={r['schur_err']:.1e}  "
                      f"3-regular={r['regular']}  det identity mod p={r['ok_modp']}")
                assert r["regular"] and r["ok_modp"] and r["schur_err"] < 1e-8

    print("\n== (3) Koenig split and det(1 + w1 + w2) on |z| = 1 ==")
    H = s3()
    r = run_identity(H, 2, rng)
    Mp, Np = r["Mp"], r["Np"]
    u1, u2, u3 = koenig(Mp, Np)
    assert mat_sum(u1, u2, u3) == Mp
    u1s = adjoint(u1, H)
    W = mat_sum(identity(Np), mat_mul(u1s, u2, H), mat_mul(u1s, u3, H))
    for z in (np.exp(0.7j), np.exp(2.3j)):
        a = np.linalg.slogdet(rho_complex(W, Np, H, z))[1]
        b = np.linalg.slogdet(rho_complex(Mp, Np, H, z))[1]
        c = np.linalg.slogdet(rho_complex(r["T"], 2, H, z))[1]
        gfac = 2 * r["g"] * H["n"] * np.log(abs(1 - z))
        print(f"z=e^i{np.angle(z):.1f}: log|det(1+w1+w2)|={a:.8f} log|det M'|={b:.8f} "
              f"log|det T| + 2g|H| log|1-z| = {c + gfac:.8f}")
        assert abs(a - b) < 1e-6 and abs(b - c - gfac) < 1e-6
    B, NB = bipartite_double(Mp, Np, H)
    rsB, csB = sums(B, NB)
    selfadj = adjoint(B, H) == B
    diag_zero = all((i, i) not in B for i in range(NB))
    print(f"B = [[0,M'],[M'*,0]]: size {NB}, self-adjoint={selfadj}, zero diagonal={diag_zero}, "
          f"row sums all 3={all(x == 3 for x in rsB)}")
    assert selfadj and diag_zero and all(x == 3 for x in rsB)

    print("\n== FK determinant over H x Z by quadrature (Mahler measure of the gadget factor is 0) ==")
    H = cyclic(2)
    # T = 2 - h s over Z/2 x Z: det rho(T(z)) = 4 - z^2, so log det_{N(H x Z)} T = log 2
    T = {}
    madd(T, 0, 0, (0, 0), 2)
    madd(T, 0, 0, (1, 1), -1)
    L, NL = linearize(T, 1)
    M1, N1 = remove_signs(L, NL)
    Mp, Np, g = pad(M1, N1)
    # log det_{N(H x Z)} X = (1/|H|) * mean over theta of log|det rho(X(e^{i theta}))|
    K = 4096
    thetas = (np.arange(K) + 0.5) * 2 * np.pi / K
    lt = np.mean([np.linalg.slogdet(rho_complex(T, 1, H, np.exp(1j * t)))[1] for t in thetas]) / H["n"]
    lm = np.mean([np.linalg.slogdet(rho_complex(Mp, Np, H, np.exp(1j * t)))[1] for t in thetas]) / H["n"]
    bias = 2 * g * np.log(2) / K  # midpoint rule: prod_k (1 - z_k) = 2 over z^K = -1
    print(f"H=Z/2, T = 2 - h s: log det T = {lt:.6f} (exact log 2 = {np.log(2):.6f}), "
          f"log det M' = {lm:.6f}, minus midpoint bias 2g log2/K = {lm - bias:.6f} "
          f"(M' size {Np}, {g} gadgets)")
    assert abs(lm - bias - np.log(2)) < 1e-6

    print("\n== (4) negative controls ==")
    H = cyclic(3)
    r = run_identity(H, 1, rng, gadget=BAD_GADGET)
    print(f"gadget with adj(G)_00 = 1-s != 0: 3-regular={r['regular']}, det identity mod p={r['ok_modp']} (expected False)")
    assert not r["ok_modp"]
    # kernel control over the finite group Z/2 (no Z variable needed): T = 1 + h has a kernel
    H = cyclic(2)
    T = {}
    madd(T, 0, 0, (0, 0), 1)
    madd(T, 0, 0, (1, 0), 1)
    L, NL = linearize(T, 1)
    M1, N1 = remove_signs(L, NL)

    def logdet_prime(X, N):
        sv = np.linalg.svd(rho_complex(X, N, H, 1.0), compute_uv=False)
        return float(np.sum(np.log(sv[sv > 1e-9]))) / H["n"]

    print(f"T = 1+h over Z/2 (kernel): log det' T = {logdet_prime(T, 1):.6f}, "
          f"log det' L = {logdet_prime(L, NL):.6f}, log det' M1 = {logdet_prime(M1, N1):.6f} "
          f"(differ: unipotent similarity does not preserve det' with kernel)")

    print("\n== (5) Theorem C(3) without ||r_B|| < 3: finite cubic graphs have atoms at +-3 ==")
    H = cyclic(2)
    r = run_identity(H, 1, rng, max_terms=1, zpow=1)
    B, NB = bipartite_double(r["Mp"], r["Np"], H)
    for q in (2, 3):
        A = finite_graph(B, NB, H, q)
        assert np.allclose(A.sum(axis=1), 3) and np.allclose(A, A.T)
        for L in (2, 3):
            for mexp in (1, 2):
                lhs, rhs, atoms, nrm = theorem_c3_check(A, L, mexp)
                print(f"q={q} |V|={A.shape[0]} L={L} m={mexp}: norm={nrm:.4f} atoms at +-3: {atoms}  "
                      f"LHS={lhs:.8f} RHS={rhs:.8f}")
                assert abs(lhs - rhs) < 1e-5 * max(1, abs(lhs))
    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()
