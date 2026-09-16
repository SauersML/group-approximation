#!/usr/bin/env python3
"""Exact finite checks for the Hochschild detection of c = [h_12(u_1), h_13(u_2)].

Toy model: A = F_p-valued functions on (Z/N)^2, Z^2 acting by translation,
R = A x| Z^2. The proof in
research/artifacts/z2-crossed-product-steinberg-kernel-nonzero-2026-09-16.md
works for every commutative unital ring A with a Z^2-action. This script checks
its identities exactly, over F_p, on random data:

  (1) the Z[Z^2]-valued cocycle identity for N_{g,h} = P_1(h_1) t_2^{h_2} P_2(g_2),
  (2) tau o b = 0 on homogeneous Hochschild 3-chains of R,
  (3) the group 2-cocycle identity for f(g,h) = tau(tr((gh)^{-1} (x) g (x) h))
      on random products of elementary and diagonal matrices in GL_3(R),
  (4) f(D1,D2) - f(D2,D1) = -1 for D1 = diag(u1,u1^-1,1), D2 = diag(u2,1,u2^-1).

Everything is exact modular arithmetic, so a pass is a proof for the sampled inputs only.
"""
import random
import numpy as np

P = 5          # characteristic
N = 3          # period of the toy model
BOX = 3        # group elements sampled from [-BOX, BOX]^2
rng = random.Random(20260916)


def act(t, m):
    """alpha_t(m)(s) = m(s + t)."""
    return np.roll(np.roll(m, -t[0], axis=0), -t[1], axis=1)


def P1(a):
    """Quantum integer: list of (exponent, sign) with P(a+b) = P(a) + t^a P(b)."""
    if a >= 0:
        return [(i, 1) for i in range(a)]
    return [(i, -1) for i in range(a, 0)]


def Ncoef(g, h):
    """N_{g,h} = P_1(h_1) t_2^{h_2} P_2(g_2) as a dict exponent -> integer."""
    out = {}
    for i, si in P1(h[0]):
        for j, sj in P1(g[1]):
            key = (i, h[1] + j)
            out[key] = out.get(key, 0) + si * sj
    return {k: v for k, v in out.items() if v}


def gr_add(x, y, sign=1):
    out = dict(x)
    for k, v in y.items():
        out[k] = out.get(k, 0) + sign * v
    return {k: v for k, v in out.items() if v}


def gr_shift(t, x):
    return {(k[0] + t[0], k[1] + t[1]): v for k, v in x.items()}


def add(g, h):
    return (g[0] + h[0], g[1] + h[1])


def check_N_identity(trials=2000):
    for _ in range(trials):
        g, h, k = [(rng.randint(-BOX, BOX), rng.randint(-BOX, BOX)) for _ in range(3)]
        lhs = gr_add(Ncoef(h, k), Ncoef(add(g, h), k), -1)
        lhs = gr_add(lhs, Ncoef(g, add(h, k)))
        lhs = gr_add(lhs, gr_shift(k, Ncoef(g, h)), -1)
        assert lhs == {}, (g, h, k, lhs)
    return True


def rand_a():
    return np.array([[rng.randrange(P) for _ in range(N)] for _ in range(N)], dtype=np.int64)


def mono_mul(x, y):
    (a, g), (b, h) = x, y
    return ((a * act(g, b)) % P, add(g, h))


def tau_mono(x0, x1, x2):
    (a0, g0), (a1, g1), (a2, g2) = x0, x1, x2
    if add(add(g0, g1), g2) != (0, 0):
        return np.zeros((N, N), dtype=np.int64)
    m = (a0 * act(g0, a1) * act(add(g0, g1), a2)) % P
    out = np.zeros((N, N), dtype=np.int64)
    for t, c in Ncoef(g1, g2).items():
        out = (out + c * act(t, m)) % P
    return out


def tau_b(x0, x1, x2, x3):
    s = tau_mono(mono_mul(x0, x1), x2, x3)
    s = s - tau_mono(x0, mono_mul(x1, x2), x3)
    s = s + tau_mono(x0, x1, mono_mul(x2, x3))
    s = s - tau_mono(mono_mul(x3, x0), x1, x2)
    return s % P


def check_tau_b(trials=3000):
    for _ in range(trials):
        gs = [(rng.randint(-BOX, BOX), rng.randint(-BOX, BOX)) for _ in range(3)]
        gs.append((-sum(g[0] for g in gs), -sum(g[1] for g in gs)))
        xs = [(rand_a(), g) for g in gs]
        assert not tau_b(*xs).any()
    return True


# ---------- matrices over R ----------
NMAT = 3


def r_zero():
    return {}


def r_add(x, y, sign=1):
    out = {k: v.copy() for k, v in x.items()}
    for g, a in y.items():
        out[g] = (out.get(g, np.zeros((N, N), dtype=np.int64)) + sign * a) % P
    return {g: a for g, a in out.items() if a.any()}


def r_mul(x, y):
    out = {}
    for g, a in x.items():
        for h, b in y.items():
            k = add(g, h)
            out[k] = (out.get(k, np.zeros((N, N), dtype=np.int64)) + a * act(g, b)) % P
    return {g: a for g, a in out.items() if a.any()}


def one_a():
    return np.ones((N, N), dtype=np.int64)


def r_one():
    return {(0, 0): one_a()}


def mat_id():
    return [[r_one() if i == j else r_zero() for j in range(NMAT)] for i in range(NMAT)]


def mat_mul(X, Y):
    Z = [[r_zero() for _ in range(NMAT)] for _ in range(NMAT)]
    for i in range(NMAT):
        for k in range(NMAT):
            acc = r_zero()
            for j in range(NMAT):
                acc = r_add(acc, r_mul(X[i][j], Y[j][k]))
            Z[i][k] = acc
    return Z


def gen_elem(i, j, r):
    M = mat_id()
    M[i][j] = r
    return M


def gen_diag(entries):
    M = mat_id()
    for i, x in enumerate(entries):
        M[i][i] = x
    return M


def rand_ring_elt(k=1):
    out = {}
    for _ in range(k):
        g = (rng.randint(-1, 1), rng.randint(-1, 1))
        out = r_add(out, {g: rand_a()})
    return out


def rand_unit_mono():
    a = np.array([[rng.randrange(1, P) for _ in range(N)] for _ in range(N)], dtype=np.int64)
    g = (rng.randint(-1, 1), rng.randint(-1, 1))
    ainv = np.vectorize(lambda v: pow(int(v), P - 2, P))(a).astype(np.int64)
    return {g: a}, {(-g[0], -g[1]): act((-g[0], -g[1]), ainv)}


def rand_word(length=2):
    """Return (M, M^{-1}) for a random product of elementary and monomial-diagonal matrices."""
    M, Minv = mat_id(), mat_id()
    for _ in range(length):
        if rng.random() < 0.6:
            i, j = rng.sample(range(NMAT), 2)
            r = rand_ring_elt()
            G, Ginv = gen_elem(i, j, r), gen_elem(i, j, r_add({}, r, -1))
        else:
            ents = [rand_unit_mono() for _ in range(NMAT)]
            G, Ginv = gen_diag([e[0] for e in ents]), gen_diag([e[1] for e in ents])
        M, Minv = mat_mul(M, G), mat_mul(Ginv, Minv)
    return M, Minv


def tau_elt(x0, x1, x2):
    out = np.zeros((N, N), dtype=np.int64)
    for g0, a0 in x0.items():
        for g1, a1 in x1.items():
            g2 = (-g0[0] - g1[0], -g0[1] - g1[1])
            if g2 in x2:
                out = (out + tau_mono((a0, g0), (a1, g1), (x2[g2], g2))) % P
    return out


def f_cocycle(G, Ginv, H, Hinv):
    GH = mat_mul(G, H)
    GHinv = mat_mul(Hinv, Ginv)
    out = np.zeros((N, N), dtype=np.int64)
    for i in range(NMAT):
        for j in range(NMAT):
            for k in range(NMAT):
                out = (out + tau_elt(GHinv[i][j], G[j][k], H[k][i])) % P
    return out, GH, GHinv


def check_group_cocycle(trials=25):
    for _ in range(trials):
        (G, Gi), (H, Hi), (K, Ki) = rand_word(), rand_word(), rand_word()
        fhk, HK, HKi = f_cocycle(H, Hi, K, Ki)
        fgh, GH, GHi = f_cocycle(G, Gi, H, Hi)
        fgh_k, _, _ = f_cocycle(GH, GHi, K, Ki)
        fg_hk, _, _ = f_cocycle(G, Gi, HK, HKi)
        assert not ((fhk - fgh_k + fg_hk - fgh) % P).any()
    return True


def check_torus_value():
    u1, u1i = {(1, 0): one_a()}, {(-1, 0): one_a()}
    u2, u2i = {(0, 1): one_a()}, {(0, -1): one_a()}
    D1, D1i = gen_diag([u1, u1i, r_one()]), gen_diag([u1i, u1, r_one()])
    D2, D2i = gen_diag([u2, r_one(), u2i]), gen_diag([u2i, r_one(), u2])
    f12, _, _ = f_cocycle(D1, D1i, D2, D2i)
    f21, _, _ = f_cocycle(D2, D2i, D1, D1i)
    val = (f12 - f21) % P
    assert (val == (P - 1)).all(), val
    return int(val[0, 0])


if __name__ == "__main__":
    print("P =", P, "N =", N)
    print("(1) N-cocycle identity in Z[Z^2]:", check_N_identity())
    print("(2) tau o b = 0 on random homogeneous 3-chains:", check_tau_b())
    print("(3) f is a group 2-cocycle on random words in GL_3(R):", check_group_cocycle())
    print("(4) f(D1,D2) - f(D2,D1) = constant", check_torus_value(), "= -1 mod", P)
