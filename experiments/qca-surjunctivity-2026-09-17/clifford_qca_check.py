#!/usr/bin/env python3
"""Calibration checks for research/clifford-qca-surjunctivity-iff-odd-stable-finiteness.

Checks (exact arithmetic on labels, float arithmetic on operators; single-threaded):

 1. Symmetric Weyl relations  W(u)W(u') = zeta^{h w(u,u')} W(u+u')  with w(u,u') = (u J u'^*)_e
    on the finite group G (Z/4 and S3), one qudit of odd dimension p per site.
 2. For T = diag(A, B^*) with AB = 1 in F_p[G]:  T J T^* = J  and  W(u) -> W(uT)  preserves the
    Weyl relations (so it defines a *-homomorphism).  Teeth: diag(A, B) (no adjoint) violates the
    relations on the nonabelian group S3, and a generic non-symplectic T fails too.
 3. Tree calibration: alpha(X_v) = X_c X_c', alpha(Z_v) = Z_c^h Z_c'^h on M_p -> M_p (x) M_p is a
    unital *-homomorphism (p-th powers, commutation phase), the generated algebra has dimension p^2
    (< p^4), X_c is trace-orthogonal to the image, and the relative commutant has dimension p^2.
    Teeth: the exponent-1 guess alpha(Z_v) = Z_c Z_c' gives phase zeta^2 != zeta.
"""
import itertools
import random
import sys

import numpy as np

random.seed(20260917)


# ----------------------------------------------------------------- groups
def cyclic(n):
    els = list(range(n))
    mul = lambda a, b: (a + b) % n
    inv = lambda a: (-a) % n
    return els, mul, inv, 0


def s3():
    els = list(itertools.permutations(range(3)))
    mul = lambda a, b: tuple(a[b[i]] for i in range(3))  # (ab)(i) = a(b(i))
    inv = lambda a: tuple(sorted(range(3), key=lambda i: a[i]))
    return els, mul, inv, (0, 1, 2)


class GroupRing:
    def __init__(self, grp, p):
        self.els, self.mul, self.inv, self.e = grp
        self.p = p
        self.idx = {g: i for i, g in enumerate(self.els)}
        self.N = len(self.els)

    def zero(self):
        return [0] * self.N

    def one(self):
        v = self.zero()
        v[self.idx[self.e]] = 1
        return v

    def rand(self):
        return [random.randrange(self.p) for _ in range(self.N)]

    def add(self, x, y):
        return [(a + b) % self.p for a, b in zip(x, y)]

    def neg(self, x):
        return [(-a) % self.p for a in x]

    def times(self, x, y):
        z = self.zero()
        for i, g in enumerate(self.els):
            if x[i] == 0:
                continue
            for j, k in enumerate(self.els):
                if y[j]:
                    t = self.idx[self.mul(g, k)]
                    z[t] = (z[t] + x[i] * y[j]) % self.p
        return z

    def star(self, x):
        z = self.zero()
        for i, g in enumerate(self.els):
            z[self.idx[self.inv(g)]] = x[i]
        return z

    def coeff_e(self, x):
        return x[self.idx[self.e]]


def mat_mul(R, X, Y):
    n, m, k = len(X), len(Y), len(Y[0])
    Z = [[R.zero() for _ in range(k)] for _ in range(n)]
    for i in range(n):
        for j in range(k):
            acc = R.zero()
            for l in range(m):
                acc = R.add(acc, R.times(X[i][l], Y[l][j]))
            Z[i][j] = acc
    return Z


def mat_star(R, X):
    return [[R.star(X[j][i]) for j in range(len(X))] for i in range(len(X[0]))]


def find_unit_pair(R, tries=20000):
    for _ in range(tries):
        A = R.rand()
        # brute force right inverse by linear algebra mod p over the regular representation
        B = solve_right_inverse(R, A)
        if B is not None and R.coeff_e(A) is not None and any(A[i] for i in range(R.N) if i != R.idx[R.e]):
            return A, B
    raise RuntimeError("no unit found")


def solve_right_inverse(R, A):
    """Solve A*B = 1 for B over F_p (Gaussian elimination)."""
    p, N = R.p, R.N
    # column j of M = A * delta_{g_j}
    cols = []
    for j in range(N):
        d = R.zero()
        d[j] = 1
        cols.append(R.times(A, d))
    M = [[cols[j][i] for j in range(N)] + [R.one()[i]] for i in range(N)]
    r = 0
    piv = []
    for c in range(N):
        pr = next((i for i in range(r, N) if M[i][c] % p), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        iv = pow(M[r][c], p - 2, p)
        M[r] = [(v * iv) % p for v in M[r]]
        for i in range(N):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    if r < N:
        return None
    B = [0] * N
    for i, c in enumerate(piv):
        B[c] = M[i][N]
    return B


# ----------------------------------------------------------------- operators
def weyl_ops(p):
    zeta = np.exp(2j * np.pi / p)
    X = np.roll(np.eye(p), 1, axis=0)  # X|j> = |j+1>
    Z = np.diag([zeta ** j for j in range(p)])
    return X, Z, zeta


def kron_all(ms):
    out = np.array([[1.0 + 0j]])
    for m in ms:
        out = np.kron(out, m)
    return out


def W_sym(R, u, X, Z, zeta, h):
    a, b = u
    ops = [np.linalg.matrix_power(X, a[i]) @ np.linalg.matrix_power(Z, b[i]) for i in range(R.N)]
    phase = zeta ** (h * sum(x * y for x, y in zip(a, b)) % R.p)
    return phase * kron_all(ops)


def omega(R, u, v):
    # (u J v^*)_e with J = [[0,-1],[1,0]]:  u J = (b, -a);  (u J v^*)_e = sum_g b(g)a'(g) - a(g)b'(g)
    a, b = u
    a2, b2 = v
    t = R.add(R.times(b, R.star(a2)), R.neg(R.times(a, R.star(b2))))
    return R.coeff_e(t)


def apply_T(R, u, T):
    row = [u[0], u[1]]
    out = []
    for j in range(2):
        acc = R.zero()
        for l in range(2):
            acc = R.add(acc, R.times(row[l], T[l][j]))
        out.append(acc)
    return out


def check_group(name, grp, p, trials=12):
    R = GroupRing(grp, p)
    X, Z, zeta = weyl_ops(p)
    h = pow(2, p - 2, p)
    J = [[R.zero(), R.neg(R.one())], [R.one(), R.zero()]]
    ok = True
    # 1. Weyl relations
    for _ in range(trials):
        u = [R.rand(), R.rand()]
        v = [R.rand(), R.rand()]
        lhs = W_sym(R, u, X, Z, zeta, h) @ W_sym(R, v, X, Z, zeta, h)
        rhs = zeta ** (h * omega(R, u, v) % p) * W_sym(R, [R.add(u[0], v[0]), R.add(u[1], v[1])], X, Z, zeta, h)
        ok &= np.allclose(lhs, rhs)
    print(f"[{name}, p={p}] symmetric Weyl relations: {ok}")
    # 2. symplectic diag(A, B^*)
    A, B = find_unit_pair(R)
    assert R.times(A, B) == R.one()
    Z0 = R.zero()
    T = [[A, Z0], [Z0, R.star(B)]]
    TJTs = mat_mul(R, mat_mul(R, T, J), mat_star(R, T))
    symp = TJTs == J
    rel = True
    for _ in range(trials):
        u = [R.rand(), R.rand()]
        v = [R.rand(), R.rand()]
        uT, vT = apply_T(R, u, T), apply_T(R, v, T)
        lhs = W_sym(R, uT, X, Z, zeta, h) @ W_sym(R, vT, X, Z, zeta, h)
        sT = apply_T(R, [R.add(u[0], v[0]), R.add(u[1], v[1])], T)
        rhs = zeta ** (h * omega(R, u, v) % p) * W_sym(R, sT, X, Z, zeta, h)
        rel &= np.allclose(lhs, rhs)
    print(f"[{name}, p={p}] A={A} B={B}: T J T^* == J: {symp}; W(u)->W(uT) preserves relations: {rel}")
    ok &= symp and rel
    # teeth: diag(A, B) without adjoint, and a random non-symplectic T
    Tbad = [[A, Z0], [Z0, B]]
    bad_symp = mat_mul(R, mat_mul(R, Tbad, J), mat_star(R, Tbad)) == J
    bad_rel = True
    for _ in range(trials):
        u = [R.rand(), R.rand()]
        v = [R.rand(), R.rand()]
        if omega(R, apply_T(R, u, Tbad), apply_T(R, v, Tbad)) != omega(R, u, v):
            bad_rel = False
    print(f"[{name}, p={p}] teeth diag(A,B): symplectic={bad_symp}, form preserved on samples={bad_rel}")
    Trand = [[R.rand(), R.rand()], [R.rand(), R.rand()]]
    rs = mat_mul(R, mat_mul(R, Trand, J), mat_star(R, Trand)) == J
    print(f"[{name}, p={p}] teeth random T: symplectic={rs}")
    return ok, bad_symp, rs


def algebra_dim(gens, dim):
    """Dimension of the unital *-algebra generated by gens (as a subspace of M_dim)."""
    basis = []

    def add(m):
        v = m.reshape(-1)
        if not basis:
            if np.linalg.norm(v) > 1e-9:
                basis.append(v / np.linalg.norm(v))
                return True
            return False
        Bm = np.array(basis).T
        coef = Bm.conj().T @ v
        r = v - Bm @ coef
        if np.linalg.norm(r) > 1e-8:
            basis.append(r / np.linalg.norm(r))
            return True
        return False

    words = [np.eye(dim, dtype=complex)]
    add(words[0])
    frontier = list(words)
    while frontier:
        new = []
        for w in frontier:
            for g in gens:
                m = w @ g
                if add(m):
                    new.append(m)
        frontier = new
    return len(basis), np.array(basis)


def check_tree(p):
    X, Z, zeta = weyl_ops(p)
    h = pow(2, p - 2, p)
    I = np.eye(p)
    aX = np.kron(X, X)
    aZ = np.kron(np.linalg.matrix_power(Z, h), np.linalg.matrix_power(Z, h))
    e = np.eye(p * p)
    pw = np.allclose(np.linalg.matrix_power(aX, p), e) and np.allclose(np.linalg.matrix_power(aZ, p), e)
    ph = np.allclose(aZ @ aX, zeta * aX @ aZ)
    ref = np.allclose(Z @ X, zeta * X @ Z)
    d, basis = algebra_dim([aX, aZ], p * p)
    Xc = np.kron(X, I).reshape(-1)
    proj = np.linalg.norm(basis.conj() @ Xc)
    # relative commutant dimension: solve [M, aX] = [M, aZ] = 0
    n = p * p
    rows = []
    for g in (aX, aZ):
        rows.append(np.kron(np.eye(n), g.T) - np.kron(g, np.eye(n)))  # vec(M g - g M) with row-major vec
    K = np.vstack(rows)
    sv = np.linalg.svd(K, compute_uv=False)
    comm = int(np.sum(sv < 1e-8)) + (K.shape[1] - len(sv))
    bZ = np.kron(Z, Z)
    teeth = np.allclose(bZ @ aX, zeta * aX @ bZ)
    print(f"[tree, p={p}] p-th powers ok: {pw}; phase zeta (target {ref}): {ph}; generated dim {d} (full {p**4});"
          f" |proj of X_c onto image| = {proj:.2e}; relative commutant dim {comm}; teeth Z_cZ_c' phase ok: {teeth}")
    return pw and ph and d == p * p and proj < 1e-9 and comm == p * p and not teeth


def W_plain(R, u, X, Z):
    a, b = u
    ops = [np.linalg.matrix_power(X, a[i]) @ np.linalg.matrix_power(Z, b[i]) for i in range(R.N)]
    return kron_all(ops)


def beta(R, u, v):
    return R.coeff_e(R.times(u[1], R.star(v[0])))


def check_plain(name, grp, p, trials=12):
    """All primes (incl. p=2): W(a,b)=X^a Z^b, W(u)W(u')=zeta^beta W(u+u'); diag(A,B^*) preserves beta."""
    R = GroupRing(grp, p)
    X, Z, zeta = weyl_ops(p)
    A, B = find_unit_pair(R)
    Z0 = R.zero()
    T = [[A, Z0], [Z0, R.star(B)]]
    rel = beta_ok = True
    for _ in range(trials):
        u = [R.rand(), R.rand()]
        v = [R.rand(), R.rand()]
        lhs = W_plain(R, u, X, Z) @ W_plain(R, v, X, Z)
        rhs = zeta ** beta(R, u, v) * W_plain(R, [R.add(u[0], v[0]), R.add(u[1], v[1])], X, Z)
        rel &= np.allclose(lhs, rhs)
        uT, vT = apply_T(R, u, T), apply_T(R, v, T)
        beta_ok &= beta(R, uT, vT) == beta(R, u, v)
        lhsT = W_plain(R, uT, X, Z) @ W_plain(R, vT, X, Z)
        sT = apply_T(R, [R.add(u[0], v[0]), R.add(u[1], v[1])], T)
        rel &= np.allclose(lhsT, zeta ** beta(R, u, v) * W_plain(R, sT, X, Z))
    print(f"[{name}, p={p}, plain Weyl] relations and W(u)->W(uT) multiplicative: {rel}; beta preserved: {beta_ok}")
    return rel and beta_ok


def main():
    allok = True
    for name, grp, p in [("S3", s3(), 2), ("Z/4", cyclic(4), 2), ("S3", s3(), 3)]:
        allok &= check_plain(name, grp, p)
    for name, grp, p in [("Z/4", cyclic(4), 3), ("S3", s3(), 3), ("Z/3", cyclic(3), 5)]:
        ok, bad_symp, rs = check_group(name, grp, p)
        allok &= ok and not rs
        if name == "S3":
            allok &= not bad_symp
    for p in (3, 5, 7):
        allok &= check_tree(p)
    print("ALL CHECKS PASS" if allok else "SOME CHECK FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
