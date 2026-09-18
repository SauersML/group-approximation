"""Check the normal p-subgroup lifting lemma for torus degree matrices.

Lemma (research/artifacts/torus-normal-p-lifting-2026-09-17.md, Lemma 3). Let N be a
finite normal p-subgroup of a group G and D in M_d(Z[G]). If p_N(D) is a unit in
M_d(Z[G/N]), then D mod p is invertible in M_d(F_p[G]); in particular xi -> xi D is
injective on Q[G]^d.

Part A (exhaustive, G = Z/6, d = 1). For every D in Z[Z/6] with coefficients in
[-2, 2]: whenever the image of D in Z[G/N] is a unit for N = <t> (p = 2) or N = <s>
(p = 3), D is invertible mod p and regular over Q. We also count the D that are
zero divisors with augmentation +-1, and check that each one has non-unit image in
BOTH quotients (as the lemma forces).

Part B (random, d <= 2). Over S_3 (N = A_3, p = 3), A_4 (N = V_4, p = 2), Z/2 x Z/6
(N = Z/2 x Z/2, p = 2) and Z/6 (N = <s>, p = 3): D = lift(U) + K, U a product of
trivial units and elementary matrices over Z[G/N], K random in M_d(omega(N) Z[G]).
Check D invertible mod p and regular over Q.

Part C (Bezout witnesses). For D = a P_s + b P_t on Z/6, S_3, A_4: the image in every
quotient by a normal p-subgroup is not a unit.

Pure Python, exact arithmetic.
"""
import random
from fractions import Fraction
from itertools import product


def compose(a, b):  # (a*b)(i) = a(b(i))
    return tuple(a[b[i]] for i in range(len(b)))


def closure(gens):
    e = tuple(range(len(gens[0])))
    elems, frontier = {e}, [e]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = compose(x, g)
                if y not in elems:
                    elems.add(y)
                    new.append(y)
        frontier = new
    return sorted(elems)


def inverse(a):
    inv = [0] * len(a)
    for i, ai in enumerate(a):
        inv[ai] = i
    return tuple(inv)


class Group:
    """Finite permutation group with a normal subgroup N and quotient data."""

    def __init__(self, gens, ngens):
        self.el = closure(gens)
        self.idx = {g: i for i, g in enumerate(self.el)}
        self.n = len(self.el)
        e = tuple(range(len(gens[0])))
        self.N = closure(ngens) if ngens else [e]
        self.mul = [[self.idx[compose(a, b)] for b in self.el] for a in self.el]
        # cosets gN (N normal, so left = right cosets)
        coset_of, reps = {}, []
        for g in self.el:
            if g in coset_of:
                continue
            c = len(reps)
            reps.append(g)
            for m in self.N:
                coset_of[compose(g, m)] = c
        self.q = [coset_of[g] for g in self.el]
        self.nq = len(reps)
        self.qmul = [[self.q[self.idx[compose(a, b)]] for b in reps] for a in reps]
        self.qrep = [self.idx[r] for r in reps]
        self.eid = self.idx[e]


def right_mult_matrix(D, d, n, mul):
    """Matrix of xi -> xi D on Z[G]^d, rows/cols indexed (g, i) -> g*d + i.
    D[i][j] is a dict {h: coeff}."""
    M = [[0] * (n * d) for _ in range(n * d)]
    for g in range(n):
        for i in range(d):
            for j in range(d):
                for h, c in D[i][j].items():
                    M[g * d + i][mul[g][h] * d + j] += c
    return M


def rank_q(M):
    A = [[Fraction(x) for x in row] for row in M]
    return _rank(A, lambda x: x, lambda a, b: a / b)


def rank_p(M, p):
    A = [[x % p for x in row] for row in M]
    return _rank(A, lambda x: x % p, lambda a, b: (a * pow(b, -1, p)) % p)


def _rank(A, red, div):
    rows, cols, r = len(A), len(A[0]) if A else 0, 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if red(A[i][c]) != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        for i in range(rows):
            if i != r and red(A[i][c]) != 0:
                f = div(A[i][c], A[r][c])
                A[i] = [red(x - f * y) for x, y in zip(A[i], A[r])]
        r += 1
    return r


def det_int(M):
    """Bareiss fraction-free determinant."""
    A = [row[:] for row in M]
    n, sign, prev = len(A), 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if A[i][k] != 0), None)
            if sw is None:
                return 0
            A[k], A[sw] = A[sw], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


def image(G, D, d):
    return [[{} if not D[i][j] else _img(G, D[i][j]) for j in range(d)] for i in range(d)]


def _img(G, x):
    out = {}
    for h, c in x.items():
        out[G.q[h]] = out.get(G.q[h], 0) + c
    return {k: v for k, v in out.items() if v}


def is_unit_quot(G, D, d):
    return abs(det_int(right_mult_matrix(image(G, D, d), d, G.nq, G.qmul))) == 1


def regular_q(G, D, d):
    return rank_q(right_mult_matrix(D, d, G.n, G.mul)) == G.n * d


def invertible_mod_p(G, D, d, p):
    return rank_p(right_mult_matrix(D, d, G.n, G.mul), p) == G.n * d


def gmat_mul(A, B, d, mul):
    C = [[{} for _ in range(d)] for _ in range(d)]
    for i in range(d):
        for j in range(d):
            out = {}
            for k in range(d):
                for g, a in A[i][k].items():
                    for h, b in B[k][j].items():
                        gh = mul[g][h]
                        out[gh] = out.get(gh, 0) + a * b
            C[i][j] = {k: v for k, v in out.items() if v}
    return C


def gmat_add(A, B, d):
    C = [[dict(A[i][j]) for j in range(d)] for i in range(d)]
    for i in range(d):
        for j in range(d):
            for h, c in B[i][j].items():
                C[i][j][h] = C[i][j].get(h, 0) + c
            C[i][j] = {k: v for k, v in C[i][j].items() if v}
    return C


def random_unit_lift(G, d, rng, steps=3):
    """Lift to M_d(Z[G]) of a product of trivial units and elementary matrices of
    M_d(Z[G/N]); the product of lifts is a lift of the product."""
    U = [[({G.eid: 1} if i == j else {}) for j in range(d)] for i in range(d)]
    for _ in range(steps):
        T = [[({G.eid: 1} if i == j else {}) for j in range(d)] for i in range(d)]
        if d == 1 or rng.random() < 0.4:
            i = rng.randrange(d)
            T[i][i] = {G.qrep[rng.randrange(G.nq)]: rng.choice([1, -1])}
        else:
            i, j = rng.sample(range(d), 2)
            T[i][j] = {G.qrep[rng.randrange(G.nq)]: rng.randint(-2, 2)
                       for _ in range(2)}
        U = gmat_mul(U, T, d, G.mul)
    return U


def random_kernel(G, d, rng, terms=3):
    """Random element of M_d(omega(N) Z[G]): sums of c (g n - g)."""
    Nidx = [G.idx[m] for m in G.N]
    K = [[{} for _ in range(d)] for _ in range(d)]
    for i in range(d):
        for j in range(d):
            for _ in range(terms):
                g, m, c = rng.randrange(G.n), rng.choice(Nidx), rng.randint(-2, 2)
                gm = G.mul[g][m]
                K[i][j][gm] = K[i][j].get(gm, 0) + c
                K[i][j][g] = K[i][j].get(g, 0) - c
            K[i][j] = {k: v for k, v in K[i][j].items() if v}
    return K


def part_a():
    t, s = (1, 0, 2, 3, 4), (0, 1, 3, 4, 2)
    gens = [t, s]
    GT, GS = Group(gens, [t]), Group(gens, [s])
    el = GT.el
    zd_aug_unit, checked = 0, {2: 0, 3: 0}
    for coeffs in product(range(-2, 3), repeat=6):
        D = [[{h: c for h, c in enumerate(coeffs) if c}]]
        if not D[0][0]:
            continue
        reg = regular_q(GT, D, 1)
        for G, p in ((GT, 2), (GS, 3)):
            if is_unit_quot(G, D, 1):
                checked[p] += 1
                assert invertible_mod_p(G, D, 1, p), (coeffs, p)
                assert reg, (coeffs, p)
        if not reg and abs(sum(coeffs)) == 1:
            zd_aug_unit += 1
            assert not is_unit_quot(GT, D, 1) and not is_unit_quot(GS, D, 1), coeffs
    print(f"Part A (Z/6, coefficients in [-2,2]): {checked[2]} D with unit image in "
          f"Z[G/<t>], {checked[3]} with unit image in Z[G/<s>]; all invertible mod p "
          f"and regular. {zd_aug_unit} zero divisors with augmentation +-1, each with "
          f"non-unit image in both quotients.")
    assert len(el) == 6


def examples():
    """(name, gens, N-gens, p, s, t) with s, t of distinct prime orders."""
    z6t, z6s = (1, 0, 2, 3, 4), (0, 1, 3, 4, 2)
    tr, cyc = (1, 0, 2), (1, 2, 0)
    a4c, v1, v2 = (1, 2, 0, 3), (1, 0, 3, 2), (2, 3, 0, 1)
    a = (1, 0, 2, 3, 4, 5, 6)
    t7, s7 = (0, 1, 3, 2, 4, 5, 6), (0, 1, 2, 3, 5, 6, 4)
    return [
        ("Z/6, N=<t>", [z6t, z6s], [z6t], 2, z6s, z6t),
        ("Z/6, N=<s>", [z6t, z6s], [z6s], 3, z6s, z6t),
        ("S_3, N=A_3", [tr, cyc], [cyc], 3, cyc, tr),
        ("A_4, N=V_4", [a4c, v1], [v1, v2], 2, a4c, v1),
        ("Z/2xZ/6, N=Z/2xZ/2", [a, t7, s7], [a, t7], 2, s7, t7),
    ]


def part_b(rng, trials=40):
    for name, gens, ngens, p, _, _ in examples():
        G = Group(gens, ngens)
        assert all(compose(compose(g, m), inverse(g)) in set(G.N)
                   for g in G.el for m in G.N), name  # N normal
        for d in (1, 2):
            for _ in range(trials):
                D = gmat_add(random_unit_lift(G, d, rng), random_kernel(G, d, rng), d)
                assert is_unit_quot(G, D, d), name
                assert invertible_mod_p(G, D, d, p), (name, d, D)
                assert regular_q(G, D, d), (name, d, D)
        print(f"Part B ({name}, p={p}): {2 * trials} random D (d = 1, 2) with unit "
              f"image in M_d(Z[G/N]); all invertible mod p and regular over Q.")


def part_c():
    for name, gens, ngens, p, s, t in examples():
        G = Group(gens, ngens)
        ps, qt = len(closure([s])), len(closure([t]))
        a = next(a for a in sorted(range(-12, 13), key=abs) if (1 - a * ps) % qt == 0)
        b = (1 - a * ps) // qt
        D = {}
        for x in closure([s]):
            D[G.idx[x]] = D.get(G.idx[x], 0) + a
        for x in closure([t]):
            D[G.idx[x]] = D.get(G.idx[x], 0) + b
        D = [[{k: v for k, v in D.items() if v}]]
        assert sum(D[0][0].values()) == 1
        zd = not regular_q(G, D, 1)
        unit = is_unit_quot(G, D, 1)
        assert zd and not unit, name
        print(f"Part C ({name}): Bezout witness {a}P_s + {b}P_t is a zero divisor with "
              f"augmentation 1, and its image in Z[G/N] is not a unit.")


if __name__ == "__main__":
    part_a()
    part_b(random.Random(20260917))
    part_c()
    print("All checks passed.")
