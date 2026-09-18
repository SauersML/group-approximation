"""Near-exact tuples of SL_n(Z) saturate the linear rank-defect scale.

Model: pi = permutation representation of SL_n(Z) on F_p^n (reduction mod p).
rho = pi on every Steinberg generator e_ij except u = e_12, where
rho(u) = pi(u) D, D = diag(lambda at x0, 1 elsewhere), |lambda| = 1, lambda^m != 1 for small m.

Every matrix here is monomial (permutation times diagonal phases), so rank(M - I) is exact:
on a cycle of length l with phase product mu, the block of M - I has rank l if mu != 1 and l - 1
if mu = 1.  Phases are tracked as integer exponents of lambda (lambda generic), so "mu != 1"
means "exponent != 0".  A numpy SVD cross-check is run on the smallest case.

Checks:
 (1) every Steinberg relator r has rank(rho(r) - I) <= |r|_u (number of u^{+-1} letters);
 (2) rank(rho(u)^L - pi(u)^L) = L for L <= p;
 (3) conversion defect rank(rho(u)^L - rho(W)) = L for the Steinberg word W = [e_13^a, e_32^b],
     ab = L, which represents e_12^L and contains no letter u;
 (4) phi(L) = rank([rho(e_12)^L, rho(e_13)^L] - I) = 2L for 2L <= p, with x0 = e_2 + e_3;
 (5) the slit origami pair of slit-origami-z2-pair-has-rank-distance-half-l has
     rank([b^s, c^s] - I) = 2 s^2 at s = floor(L/2) (quadratic, not linear).
"""
import itertools
import sys


class Mono:
    """Monomial matrix on {0..N-1}: basis vector x -> lambda^ph[x] * basis vector perm[x]."""

    def __init__(self, perm, ph):
        self.perm = perm
        self.ph = ph

    def __mul__(self, other):  # (self * other)(x) = self(other(x))
        N = len(self.perm)
        perm = [self.perm[other.perm[x]] for x in range(N)]
        ph = [other.ph[x] + self.ph[other.perm[x]] for x in range(N)]
        return Mono(perm, ph)

    def inv(self):
        N = len(self.perm)
        perm = [0] * N
        ph = [0] * N
        for x in range(N):
            perm[self.perm[x]] = x
            ph[self.perm[x]] = -self.ph[x]
        return Mono(perm, ph)

    def rank_minus_I(self):
        N = len(self.perm)
        seen = [False] * N
        r = 0
        for x in range(N):
            if seen[x]:
                continue
            l, mu, y = 0, 0, x
            while not seen[y]:
                seen[y] = True
                mu += self.ph[y]
                y = self.perm[y]
                l += 1
            r += l if mu != 0 else l - 1
        return r


def identity(N):
    return Mono(list(range(N)), [0] * N)


def power(M, e):
    N = len(M.perm)
    R = identity(N)
    B = M if e >= 0 else M.inv()
    for _ in range(abs(e)):
        R = B * R
    return R


def comm(A, B):
    return A * B * A.inv() * B.inv()


def build(n, p):
    pts = list(itertools.product(range(p), repeat=n))
    idx = {v: i for i, v in enumerate(pts)}
    N = len(pts)

    def elem(i, j):
        perm = [0] * N
        for v, a in idx.items():
            w = list(v)
            w[i] = (w[i] + w[j]) % p
            perm[a] = idx[tuple(w)]
        return Mono(perm, [0] * N)

    E = {(i, j): elem(i, j) for i in range(n) for j in range(n) if i != j}
    return pts, idx, N, E


def perturbed(E, idx, N, n, x0):
    rho = dict(E)
    D = Mono(list(range(N)), [1 if a == idx[x0] else 0 for a in range(N)])
    rho[(0, 1)] = E[(0, 1)] * D  # rho(u) = pi(u) D
    return rho


def steinberg_relators(n):
    """Words as lists of ((i,j), exponent) over the elementary generators."""
    rels = []
    gens = [(i, j) for i in range(n) for j in range(n) if i != j]
    for (i, j) in gens:
        for (k, l) in gens:
            if (i, j) >= (k, l):
                continue
            if j == k and i != l:  # [e_ij, e_jl] = e_il
                rels.append([((i, j), 1), ((j, l), 1), ((i, j), -1), ((j, l), -1), ((i, l), -1)])
            elif l == i and k != j:  # [e_ki, e_ij] = e_kj
                rels.append([((k, l), 1), ((i, j), 1), ((k, l), -1), ((i, j), -1), ((k, j), -1)])
            elif j != k and i != l:
                rels.append([((i, j), 1), ((k, l), 1), ((i, j), -1), ((k, l), -1)])
    # (e_12 e_21^{-1} e_12)^4 = 1
    rels.append([((0, 1), 1), ((1, 0), -1), ((0, 1), 1)] * 4)
    return rels


def evaluate(rho, word, N):
    R = identity(N)
    for g, e in word:
        R = R * power(rho[g], e)
    return R


def main():
    out = []
    ok = True
    for (n, p) in [(3, 11), (3, 13), (4, 7)]:
        pts, idx, N, E = build(n, p)
        x0 = tuple([0, 1, 1] + [0] * (n - 3))
        rho = perturbed(E, idx, N, n, x0)
        # (0) the exact pi satisfies the relators
        for r in steinberg_relators(n):
            if evaluate(E, r, N).rank_minus_I() != 0:
                ok = False
                out.append(f"pi fails relator {r}")
        # (1)
        worst = 0
        for r in steinberg_relators(n):
            ru = sum(1 for g, e in r if g == (0, 1))
            rk = evaluate(rho, r, N).rank_minus_I()
            worst = max(worst, rk)
            if rk > ru:
                ok = False
                out.append(f"relator rank {rk} > |r|_u {ru}: {r}")
        out.append(f"SL_{n}(Z) mod {p}, d={N}: max relator rank = {worst} (each relator r checked: rank <= |r|_u; the Weyl relator has |r|_u = 8)")
        u, v = (0, 1), (0, 2)
        for L in range(1, p // 2 + 1):
            conv0 = (power(rho[u], L) * power(E[u], -L)).rank_minus_I()
            # W = [e_13^a, e_32^b] = e_12^{ab}; pick a = 1, b = L and a factorization if available
            facts = [(a, L // a) for a in range(1, L + 1) if L % a == 0]
            convs = []
            for a, b in facts:
                W = [((0, 2), a), ((2, 1), b), ((0, 2), -a), ((2, 1), -b)]
                piW = evaluate(E, W, N)
                if (piW * power(E[u], -L)).rank_minus_I() != 0:
                    ok = False
                    out.append(f"W=[e13^{a},e32^{b}] != e12^{L} mod {p}")
                convs.append((power(rho[u], L) * evaluate(rho, W, N).inv()).rank_minus_I())
            ph = comm(power(rho[u], L), power(rho[v], L)).rank_minus_I()
            good = conv0 == L and all(c == L for c in convs) and ph == 2 * L
            ok = ok and good
            out.append(f"  L={L}: rank(rho(u)^L - pi(u)^L)={conv0}, conversion defects={convs}, phi(L)={ph}  {'OK' if good else 'FAIL'}")
    # numpy cross-check on SL_3 mod 5
    try:
        import numpy as np
        pts, idx, N, E = build(3, 5)
        rho = perturbed(E, idx, N, 3, (0, 1, 1))
        lam = np.exp(2j * np.pi * 0.2360679)

        def dense(M):
            A = np.zeros((N, N), dtype=complex)
            for x in range(N):
                A[M.perm[x], x] = lam ** M.ph[x]
            return A
        for L in (1, 2):
            A = dense(comm(power(rho[(0, 1)], L), power(rho[(0, 2)], L))) - np.eye(N)
            r = np.linalg.matrix_rank(A, tol=1e-8)
            out.append(f"numpy cross-check SL_3 mod 5, L={L}: phi = {r} (expected {2*L})")
            ok = ok and r == 2 * L
    except ImportError:
        out.append("numpy not available; skipped cross-check")
    # (5) slit origami
    for Lt in range(4, 15, 2):
        s = Lt // 2
        sq = [(i, x, y) for i in range(2) for x in range(Lt) for y in range(Lt)]
        ix = {q: a for a, q in enumerate(sq)}
        N = len(sq)
        sig = Mono([ix[(i, (x + 1) % Lt, y)] for (i, x, y) in sq], [0] * N)
        tau = Mono([ix[(1 - i, x, 1)] if (y == 0 and x < s) else ix[(i, x, (y + 1) % Lt)] for (i, x, y) in sq], [0] * N)
        c1 = comm(sig, tau).rank_minus_I()
        profile = [comm(power(sig, m), power(tau, m)).rank_minus_I() for m in range(1, s + 1)]
        good = c1 == 2 and profile[-1] == 2 * s * s
        ok = ok and good
        out.append(f"slit origami L={Lt}, d={N}: rank([b,c]-I)={c1}, phi(m) for m=1..{s}: {profile}; 2s^2={2*s*s}  {'OK' if good else 'FAIL'}")
    out.append("ALL OK" if ok else "SOME CHECK FAILED")
    print("\n".join(out))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
