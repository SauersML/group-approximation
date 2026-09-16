#!/usr/bin/env python3
"""Checks for irs-rigid-triangle-colimit-sofic-iff-one-letter-model (2026-09-16).

Part 1: orders of the (2,4,6) Levi groups L_ij = T.(rank-two group), the lcm that every
        one-letter model degree must be divisible by (up to |Z|), the ranks
        r = 1 + [L_ij:T] - [L_ij:L_i] - [L_ij:L_j] of the vertex relator kernels, the
        orbifold Euler characteristic times |T|, and |ker(A mod q-1)| on (Z/(q-1))^3
        (the centre, ASSUMING Z = common kernel of the simple roots on T; not read at source).
Part 2: randomized tests of the rounding lemma (Lemma A) and the alignment lemma (Lemma B)
        of the route, on small finite groups given by their multiplication tables.
Single-threaded, deterministic seed, runs in seconds.
"""
import itertools
import random
from math import gcd
from functools import reduce


def lcm(a, b):
    return a * b // gcd(a, b)


# ---------------------------------------------------------------- Part 1
def levi_data(q):
    T = (q - 1) ** 3
    LiT = q * (q + 1)                                     # [L_i : T]
    L12T = LiT ** 2                                       # SL_2 x SL_2 over its torus
    L13T = q**4 * (q**4 - 1) * (q**2 - 1) // (q - 1) ** 2  # Sp_4(q) over its torus
    L23T = q**6 * (q**6 - 1) * (q + 1) // (q - 1)          # G_2(q) over its torus
    orders = {'L_i': T * LiT, 'L_12': T * L12T, 'L_13': T * L13T, 'L_23': T * L23T}
    N = reduce(lcm, [orders['L_12'], orders['L_13'], orders['L_23']])
    ranks = {k: 1 + v - 2 * (v // LiT) for k, v in [('L_12', L12T), ('L_13', L13T), ('L_23', L23T)]}
    chiT = 1 - 3 / LiT + 1 / L12T + 1 / L13T + 1 / L23T
    return orders, N, ranks, chiT


A = [[2, 0, -1], [0, 2, -1], [-2, -3, 2]]


def kernel_size_mod(m):
    """|{v in (Z/m)^3 : v A = 0}| and |{v : A v = 0}| by brute force."""
    rows = cols = 0
    for v in itertools.product(range(m), repeat=3):
        if all(sum(v[i] * A[i][j] for i in range(3)) % m == 0 for j in range(3)):
            rows += 1
        if all(sum(A[i][j] * v[j] for j in range(3)) % m == 0 for i in range(3)):
            cols += 1
    return rows, cols


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


print('Part 1: (2,4,6) Levi triangle data')
print('det A =', det3(A))
for q in [4, 5, 7, 8, 9]:
    orders, N, ranks, chiT = levi_data(q)
    zr, zc = kernel_size_mod(q - 1)
    print(f'q={q}: |L_i|={orders["L_i"]} |L_12|={orders["L_12"]} |L_13|={orders["L_13"]} '
          f'|L_23|={orders["L_23"]}')
    print(f'      lcm(|L_ij|)={N}  ranks r(L_12,L_13,L_23)={ranks["L_12"]},{ranks["L_13"]},'
          f'{ranks["L_23"]}  chi*|T|={chiT:.6f}  |ker A mod {q-1}| rows/cols = {zr}/{zc}')
assert levi_data(4)[1] == 12831436800
assert levi_data(4)[2]['L_23'] == 25159681


# ---------------------------------------------------------------- Part 2
def perm_group_elements(gens, n):
    """Closure of permutation generators on range(n); elements as tuples."""
    e = tuple(range(n))
    elems = {e}
    frontier = [e]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                h = tuple(s[g[i]] for i in range(n))   # h = s o g
                if h not in elems:
                    elems.add(h)
                    new.append(h)
        frontier = new
    return sorted(elems)


def compose(a, b):          # (a o b)(i) = a[b[i]]
    return tuple(a[b[i]] for i in range(len(b)))


def inverse(a):
    inv = [0] * len(a)
    for i, ai in enumerate(a):
        inv[ai] = i
    return tuple(inv)


def hamming(a, b):
    return sum(1 for i in range(len(a)) if a[i] != b[i]) / len(a)


def free_action(H, mult, m, rng):
    """Free action of H on d = |H| m points: m regular orbits, randomly relabelled."""
    n = len(H)
    d = n * m
    lab = list(range(d))
    rng.shuffle(lab)
    # point (j, k) = lab[j*n + k] ; g acts by left multiplication on k
    act = {}
    for gi in range(n):
        p = [0] * d
        for j in range(m):
            for k in range(n):
                p[lab[j * n + k]] = lab[j * n + mult[gi][k]]
        act[gi] = tuple(p)
    return act


def random_transpositions(d, k, rng):
    p = list(range(d))
    for _ in range(k):
        a, b = rng.randrange(d), rng.randrange(d)
        p[a], p[b] = p[b], p[a]
    return tuple(p)


def round_almost_action(sigma, mult, e_index):
    """Lemma A construction. sigma: dict g -> permutation. Returns rho."""
    n = len(sigma)
    d = len(sigma[0])
    X0 = [x for x in range(d)
          if sigma[e_index][x] == x and all(sigma[mult[g][h]][x] == sigma[g][sigma[h][x]]
                                            for g in range(n) for h in range(n))]
    X0set = set(X0)
    X1 = [x for x in X0 if all(sigma[k][x] in X0set for k in range(n))]
    Y = set()
    for x in X1:
        for k in range(n):
            Y.add(sigma[k][x])
    rho = {}
    for g in range(n):
        rho[g] = tuple(sigma[g][x] if x in Y else x for x in range(d))
    return rho


def align(alpha, beta):
    """Lemma B construction: pi with pi alpha(h) pi^-1 = beta(h), supp pi in D."""
    n = len(alpha)
    d = len(alpha[0])
    D = [p for p in range(d) if any(alpha[h][p] != beta[h][p] for h in range(n))]
    Dset = set(D)
    pi = list(range(d))
    seen_a, seen_b = set(), set()
    reps_a, reps_b = [], []
    for p in D:
        if p not in seen_a:
            reps_a.append(p)
            seen_a.update(alpha[h][p] for h in range(n))
        if p not in seen_b:
            reps_b.append(p)
            seen_b.update(beta[h][p] for h in range(n))
    assert len(reps_a) == len(reps_b) and seen_a == Dset == seen_b
    for pa, pb in zip(reps_a, reps_b):
        for h in range(n):
            pi[alpha[h][pa]] = beta[h][pb]
    return tuple(pi), D


def small_group(name):
    if name == 'S3':
        gens = [(1, 0, 2), (1, 2, 0)]
        n = 3
    elif name == 'A4':
        gens = [(1, 2, 0, 3), (1, 0, 3, 2)]
        n = 4
    elif name == 'S4':
        gens = [(1, 0, 2, 3), (1, 2, 3, 0)]
        n = 4
    H = perm_group_elements(gens, n)
    idx = {g: i for i, g in enumerate(H)}
    mult = [[idx[compose(H[g], H[h])] for h in range(len(H))] for g in range(len(H))]
    e_index = idx[tuple(range(n))]
    return H, mult, e_index


print('\nPart 2: randomized tests of Lemma A (rounding) and Lemma B (alignment)')
rng = random.Random(20260916)
worst_A = 0.0
worst_B = 0.0
for name in ['S3', 'A4', 'S4']:
    H, mult, e_index = small_group(name)
    n = len(H)
    for trial in range(40):
        m = rng.randrange(20, 60)
        rho0 = free_action(H, mult, m, rng)
        d = n * m
        k = rng.randrange(0, 4)
        sigma = {g: compose(rho0[g], random_transpositions(d, k, rng)) for g in range(n)}
        delta = max([hamming(sigma[mult[g][h]], compose(sigma[g], sigma[h]))
                     for g in range(n) for h in range(n)]
                    + [hamming(sigma[e_index], tuple(range(d)))])
        rho = round_almost_action(sigma, mult, e_index)
        for g in range(n):
            for h in range(n):
                assert rho[mult[g][h]] == compose(rho[g], rho[h]), 'rounding not a homomorphism'
        dist = max(hamming(rho[g], sigma[g]) for g in range(n))
        bound = (n + 1) * (n * n + 1) * delta
        assert dist <= bound + 1e-12, (name, dist, bound)
        if delta > 0:
            worst_A = max(worst_A, dist / bound)
        # Lemma B: two free actions agreeing off a small invariant set
        alpha = rho0
        c = rng.randrange(0, max(1, m // 5))       # re-randomize c orbits
        orbit_pts = sorted(set(alpha[h][p] for p in range(0, d) for h in range(n)))
        # choose c random alpha-orbits and replace the action there by a relabelled one
        pts = list(range(d))
        rng.shuffle(pts)
        chosen, used = [], set()
        for p in pts:
            if len(chosen) >= c:
                break
            if p not in used:
                orb = [alpha[h][p] for h in range(n)]
                chosen.append(orb)
                used.update(orb)
        U = sorted(used)
        perm_u = U[:]
        rng.shuffle(perm_u)
        relab = list(range(d))
        for a, b in zip(U, perm_u):
            relab[a] = b
        relab = tuple(relab)
        beta = {h: compose(compose(relab, alpha[h]), inverse(relab)) for h in range(n)}
        pi, D = align(alpha, beta)
        for h in range(n):
            assert compose(compose(pi, alpha[h]), inverse(pi)) == beta[h], 'alignment failed'
        supp = [p for p in range(d) if pi[p] != p]
        assert set(supp) <= set(D)
        mism = max(hamming(alpha[h], beta[h]) for h in range(n))
        assert len(D) <= n * mism * d + 1e-9
        # conjugation cost (F2) on a random permutation
        psi = random_transpositions(d, 50, rng)
        cost = hamming(compose(compose(pi, psi), inverse(pi)), psi)
        assert cost <= 2 * len(supp) / d + 1e-12
        if supp:
            worst_B = max(worst_B, cost / (2 * len(supp) / d))
    print(f'{name}: 40 trials passed (|H|={n})')
print(f'max observed dist/bound in Lemma A: {worst_A:.4f}; max cost/bound in (F2): {worst_B:.4f}')


# ---------------------------------------------------------------- Part 3
# Euler characteristic of the spanning-tree amalgam K_0 = (X_12 *_{X_1} X_13) *_{X_3} X_23,
# chi(K_0) = sum 1/|X_ij| - 1/|X_1| - 1/|X_3|, and the rank 1 - [K_0:M] chi(K_0) of a
# torsion-free subgroup M of finite index. X = L/Z with |Z| = |ker A mod (q-1)| (ASSUMED).
from fractions import Fraction
print('\nPart 3: Euler characteristic of K_0 and free rank of torsion-free M')
for q in [4, 5, 7, 8, 9]:
    orders, N, ranks, chiT = levi_data(q)
    z = kernel_size_mod(q - 1)[0]
    X = {k: v // z for k, v in orders.items()}
    chiK0 = (Fraction(1, X['L_12']) + Fraction(1, X['L_13']) + Fraction(1, X['L_23'])
             - Fraction(2, X['L_i']))
    Nz = N // z
    rank_min = 1 - Nz * chiK0
    assert chiK0 < 0 and rank_min.denominator == 1
    print(f'q={q}: |Z|={z} chi(K_0)={float(chiK0):.6e}  lcm|X_ij|={Nz}  '
          f'rank of M at index lcm = {rank_min}  |X_2|={X["L_i"]}')
print('all checks passed')
