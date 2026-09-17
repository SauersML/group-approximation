#!/usr/bin/env python3
"""Sanity checks for kun-thom-actor-strong-atiyah-via-formal-torus.

The characteristic-zero Kun--Thom actor is G_0 = EL_r(R) x| SL_d(Z),
R = Z[x_1^{+-1},...,x_d^{+-1}], with A acting by x^v -> x^{Av}.
The formal torus map iota: R -> Z_p[[u_1..u_d]], x_i -> 1+u_i, and the
substitutions sigma_A(u_i) = prod_j (1+u_j)^{A_ji} - 1 give homomorphisms

    phi_n : GL_r(R) x| SL_d(Z) -> GL_r(Z_p[[u]]/(u)^n) x| SL_d(Z_p),
            (M, A) -> (iota(M) mod u^n, A).

Everything is computed modulo (p^k, u^n), which is exact for the checked
identities: they are identities in Z[[u]]/(u)^n with integer coefficients.

Checks:
 1. iota(alpha_A(f)) = sigma_A(iota(f)) on random Laurent polynomials.
 2. sigma_A sigma_B = sigma_AB on the generators u_i.
 3. phi_n(g g') = phi_n(g) phi_n(g') on random elements of GL_r(R) x| SL_d(Z).
 4. The chain is strict: e_12(p (x_1 - 1)^n) lies in K, is killed by phi_n and
    not by phi_{n+1}.
 5. Formal torsion-freeness: for random X in M_r((u)) with X != 0 mod u^n,
    (I+X)^p != I mod u^n (checked with p = 3 and p = 2).
 6. The calibration failure at p = 2: -I lies in K and in the congruence
    group, and has order 2.
 7. The infranormal pair in characteristic zero: alpha_A maps Z[x] into itself
    for nonnegative A, and A = I - E_12 sends x_2 to x_1^{-1} x_2.

Run: python3 check_formal_torus.py   (pure Python, single thread, < 1 min)
"""
import itertools
import random
import sys

random.seed(20260917)


def binom(a, j):
    """Generalized binomial coefficient for integer a (possibly negative)."""
    num = 1
    for i in range(j):
        num *= (a - i)
    den = 1
    for i in range(1, j + 1):
        den *= i
    assert num % den == 0
    return num // den


class Trunc:
    """Z/(MOD)[u_1..u_d]/(u)^n as dict monomial-tuple -> coefficient."""

    def __init__(self, d, n, mod):
        self.d, self.n, self.mod = d, n, mod
        self.monos = [m for m in itertools.product(range(n), repeat=d) if sum(m) < n]

    def clean(self, f):
        return {m: c % self.mod for m, c in f.items() if c % self.mod and sum(m) < self.n}

    def one(self):
        return {tuple([0] * self.d): 1}

    def add(self, f, g):
        h = dict(f)
        for m, c in g.items():
            h[m] = h.get(m, 0) + c
        return self.clean(h)

    def neg(self, f):
        return self.clean({m: -c for m, c in f.items()})

    def mul(self, f, g):
        h = {}
        for m1, c1 in f.items():
            s1 = sum(m1)
            for m2, c2 in g.items():
                if s1 + sum(m2) >= self.n:
                    continue
                m = tuple(a + b for a, b in zip(m1, m2))
                h[m] = h.get(m, 0) + c1 * c2
        return self.clean(h)

    def one_plus_u_pow(self, i, a):
        f = {}
        for j in range(self.n):
            m = [0] * self.d
            m[i] = j
            f[tuple(m)] = binom(a, j)
        return self.clean(f)

    def torus_monomial(self, v):
        """iota(x^v) = prod_i (1+u_i)^{v_i}."""
        f = self.one()
        for i, a in enumerate(v):
            f = self.mul(f, self.one_plus_u_pow(i, a))
        return f

    def iota(self, laurent):
        f = {}
        for v, c in laurent.items():
            f = self.add(f, {m: c * x for m, x in self.torus_monomial(v).items()})
        return f

    def sigma_images(self, A):
        """T_i = sigma_A(u_i) = iota(x^{A e_i}) - 1."""
        d = self.d
        return [self.add(self.torus_monomial([A[j][i] for j in range(d)]), self.neg(self.one()))
                for i in range(d)]

    def substitute(self, f, T):
        # powers cache
        pw = [[self.one()] for _ in range(self.d)]
        for i in range(self.d):
            for _ in range(1, self.n):
                pw[i].append(self.mul(pw[i][-1], T[i]))
        h = {}
        for m, c in f.items():
            term = {tuple([0] * self.d): c}
            for i, e in enumerate(m):
                term = self.mul(term, pw[i][e])
            h = self.add(h, term)
        return h

    def sigma(self, A, f):
        return self.substitute(f, self.sigma_images(A))


def matmul_int(A, B):
    d = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(d)) for j in range(d)] for i in range(d)]


def alpha(A, laurent):
    d = len(A)
    out = {}
    for v, c in laurent.items():
        w = tuple(sum(A[i][j] * v[j] for j in range(d)) for i in range(d))
        out[w] = out.get(w, 0) + c
    return {w: c for w, c in out.items() if c}


def random_laurent(d, terms=3, span=2, coef=4):
    return {tuple(random.randint(-span, span) for _ in range(d)): random.randint(-coef, coef)
            for _ in range(terms)}


def random_sl(d, steps=6, p=None):
    A = [[int(i == j) for j in range(d)] for i in range(d)]
    for _ in range(steps):
        i, j = random.sample(range(d), 2)
        lam = random.choice([-1, 1]) * (p if p else 1)
        E = [[int(a == b) for b in range(d)] for a in range(d)]
        E[i][j] = lam
        A = matmul_int(A, E)
    return A


# ---- Laurent matrices -------------------------------------------------------

def lmat_id(r, d):
    return [[({tuple([0] * d): 1} if i == j else {}) for j in range(r)] for i in range(r)]


def l_add(f, g):
    h = dict(f)
    for m, c in g.items():
        h[m] = h.get(m, 0) + c
    return {m: c for m, c in h.items() if c}


def l_mul(f, g):
    h = {}
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            h[m] = h.get(m, 0) + c1 * c2
    return {m: c for m, c in h.items() if c}


def lmat_mul(M, N):
    r = len(M)
    return [[{m: c for m, c in
              _sum([l_mul(M[i][k], N[k][j]) for k in range(r)]).items() if c}
             for j in range(r)] for i in range(r)]


def _sum(fs):
    h = {}
    for f in fs:
        h = l_add(h, f)
    return h


def random_elementary_product(r, d, p, steps=3):
    """Random product of e_ij(p * f) with f a random Laurent polynomial: lies in K."""
    M = lmat_id(r, d)
    for _ in range(steps):
        i, j = random.sample(range(r), 2)
        E = lmat_id(r, d)
        E[i][j] = {v: p * c for v, c in random_laurent(d, terms=2).items() if c}
        M = lmat_mul(M, E)
    return M


def lmat_alpha(A, M):
    return [[alpha(A, f) for f in row] for row in M]


# ---- truncated matrices -------------------------------------------------------

def tmat_mul(T, X, Y):
    r = len(X)
    return [[_tsum(T, [T.mul(X[i][k], Y[k][j]) for k in range(r)]) for j in range(r)] for i in range(r)]


def _tsum(T, fs):
    h = {}
    for f in fs:
        h = T.add(h, f)
    return h


def tmat_iota(T, M):
    return [[T.iota(f) for f in row] for row in M]


def tmat_sigma(T, A, X):
    Ts = T.sigma_images(A)
    return [[T.substitute(f, Ts) for f in row] for row in X]


def tmat_eq(X, Y):
    return all(X[i][j] == Y[i][j] for i in range(len(X)) for j in range(len(X)))


def tmat_id(T, r):
    return [[(T.one() if i == j else {}) for j in range(r)] for i in range(r)]


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        global FAILED
        FAILED = True


FAILED = False


def main():
    d, r, p, n, k = 3, 3, 3, 4, 6
    T = Trunc(d, n, p ** k)

    # 1. intertwining
    ok = True
    for _ in range(25):
        A = random_sl(d, p=p)
        f = random_laurent(d)
        if T.iota(alpha(A, f)) != T.sigma(A, T.iota(f)):
            ok = False
    check("1. iota o alpha_A = sigma_A o iota  (d=3, p=3, mod 3^6, u^4; 25 samples)", ok)
    # negative control: the transpose substitution must NOT intertwine
    A = [[1, 3, 0], [0, 1, 0], [3, 9, 1]]
    At = [list(row) for row in zip(*A)]
    f = {(1, -2, 1): 2, (0, 1, 0): -1}
    check("1'. negative control: alpha_(A^T) does not intertwine with sigma_A",
          T.iota(alpha(At, f)) != T.sigma(A, T.iota(f)))

    # 2. sigma_A sigma_B = sigma_AB
    ok = True
    for _ in range(10):
        A, B = random_sl(d), random_sl(d)
        AB = matmul_int(A, B)
        TB = T.sigma_images(B)
        lhs = [T.sigma(A, TB[i]) for i in range(d)]
        rhs = T.sigma_images(AB)
        if lhs != rhs:
            ok = False
    check("2. sigma_A sigma_B = sigma_AB on u_1..u_3 (10 samples)", ok)

    # 3. homomorphism property on H = K x| Gamma_3(3)
    ok = True
    for _ in range(4):
        M, A = random_elementary_product(r, d, p), random_sl(d, p=p)
        N, B = random_elementary_product(r, d, p), random_sl(d, p=p)
        prod_M = lmat_mul(M, lmat_alpha(A, N))
        prod_A = matmul_int(A, B)
        lhs = (tmat_iota(T, prod_M), prod_A)
        X, Y = tmat_iota(T, M), tmat_iota(T, N)
        rhs = (tmat_mul(T, X, tmat_sigma(T, A, Y)), matmul_int(A, B))
        if not (tmat_eq(lhs[0], rhs[0]) and lhs[1] == rhs[1]):
            ok = False
        # image lies in the congruence group: iota(M) = I mod (p, u)
        for i in range(r):
            for j in range(r):
                c0 = X[i][j].get(tuple([0] * d), 0)
                if (c0 - int(i == j)) % p:
                    ok = False
    check("3. phi_n is a homomorphism on H and lands in I + M_r((p,u)) (4 samples)", ok)

    # 4. strict chain
    Tn1 = Trunc(d, n + 1, p ** k)
    f = {}
    for j in range(n + 1):  # p*(x_1 - 1)^n
        v = (j, 0, 0)
        f[v] = p * binom(n, j) * (-1) ** (n - j)
    e = lmat_id(r, d)
    e[0][1] = {v: c for v, c in f.items() if c}
    killed_n = tmat_eq(tmat_iota(T, e), tmat_id(T, r))
    killed_n1 = tmat_eq(tmat_iota(Tn1, e), tmat_id(Tn1, r))
    check("4. e_12(p (x_1-1)^n) in K is killed by phi_n but not by phi_(n+1)",
          killed_n and not killed_n1)

    # 5. no p-torsion in I + M_r((u)) mod u^n, for p = 3 and p = 2
    for pp in (3, 2):
        Tp = Trunc(d, n, pp ** k)
        ok = True
        for _ in range(20):
            X = [[{} for _ in range(r)] for _ in range(r)]
            deg = random.randint(1, n - 1)
            for i in range(r):
                for j in range(r):
                    for m in Tp.monos:
                        if sum(m) >= deg and random.random() < 0.3:
                            X[i][j][m] = random.randint(0, pp ** k - 1)
                X[i] = [Tp.clean(x) for x in X[i]]
            if all(not X[i][j] for i in range(r) for j in range(r)):
                continue
            g = [[Tp.add(X[i][j], Tp.one() if i == j else {}) for j in range(r)] for i in range(r)]
            gp = g
            for _ in range(pp - 1):
                gp = tmat_mul(Tp, gp, g)
            # g^p = I would force the lowest degree part of X to be killed by p;
            # over Z/p^k this only happens if that part is divisible by p^(k-1).
            low = min(sum(m) for i in range(r) for j in range(r) for m in X[i][j])
            lowpart_div = all((c % pp ** (k - 1)) == 0 for i in range(r) for j in range(r)
                              for m, c in X[i][j].items() if sum(m) == low)
            if tmat_eq(gp, tmat_id(Tp, r)) and not lowpart_div:
                ok = False
        check("5. (I+X)^%d != I mod u^%d for X in M_3((u)) with p-primitive lowest part (p=%d)"
              % (pp, n, pp), ok)

    # 6. p = 2 calibration: -I is in K(2) and has order two
    minusI = [[({(0, 0, 0): -1} if i == j else {}) for j in range(r)] for i in range(r)]
    T2 = Trunc(d, n, 2 ** k)
    X = tmat_iota(T2, minusI)
    in_cong = all(((X[i][j].get((0, 0, 0), 0) - int(i == j)) % 2 == 0) for i in range(r) for j in range(r))
    order2 = tmat_eq(tmat_mul(T2, X, X), tmat_id(T2, r)) and not tmat_eq(X, tmat_id(T2, r))
    check("6. p=2: -I in K and in I + M_r((2,u)), of order 2 (method must and does fail)",
          in_cong and order2)

    # 7. infranormal pair data
    ok = True
    for _ in range(20):
        A = [[random.randint(0, 2) for _ in range(d)] for _ in range(d)]
        f = {tuple(random.randint(0, 3) for _ in range(d)): 1 for _ in range(3)}
        if any(min(w) < 0 for w in alpha(A, f)):
            ok = False
    A = [[1, -1, 0], [0, 1, 0], [0, 0, 1]]
    ok = ok and alpha(A, {(0, 1, 0): 1}) == {(-1, 1, 0): 1}
    check("7. nonnegative A compress Z[x]; A = I - E_12 sends x_2 -> x_1^-1 x_2", ok)

    print("ALL PASS" if not FAILED else "SOME CHECK FAILED")
    return 1 if FAILED else 0


if __name__ == "__main__":
    sys.exit(main())
