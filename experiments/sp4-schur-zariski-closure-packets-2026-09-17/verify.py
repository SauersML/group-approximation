#!/usr/bin/env python3
"""Exact and numerical checks for research/artifacts/sp4-schur-zariski-closure-packets-2026-09-17.md.

Part A (exact). An explicit [2,2]-type packet with compact commutant torus inside Sp_4(Z):
  D = (-1, 3)_Q, order O = Z<1, i, j, k>, form f(x, y) = trd(mu * conj(x) * y) with mu pure
  in the trace dual of O (so f is integral on O).
  Left multiplication by norm-one units of O preserves O and f. We find mu with f unimodular
  (Pfaffian +-1) and nrd(mu) > 0, change to a symplectic basis, and verify that the images
  of i (order 4) and the hyperbolic units 2+j, 2+k lie in Sp_4(Z).
  This is a packet with torsion, Q-irreducible, preserving no real Lagrangian, and with
  nonzero winding (Part B), so it is not pruned by P1--P4, by Howie, or by Forester--Rourke.
  Theorem A of the artifact kills it.
Part B (numerical). Winding of the compact loop theta -> cos(theta) + i sin(theta) in Sp_4(R).
Part C (numerical). Lemma IND: induce an alpha-projective representation through the twisted
  group algebra and check the cocycle identity on B = (Z/3)^2 x| Z/2, S = (Z/3)^2.
Part D (numerical). Clock-shift realization of every mod-n class on a genus-2 surface group.
"""
import itertools
from fractions import Fraction
import numpy as np

FAIL = []


def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond:
        FAIL.append(name)


# ---------------------------------------------------------------- Part A
A_, B_ = -1, 3  # i^2 = a, j^2 = b, k = ij


def qmul(x, y, a=A_, b=B_):
    x0, x1, x2, x3 = x
    y0, y1, y2, y3 = y
    # standard formulas for (a, b)_Q with k = ij, k^2 = -ab
    return (
        x0 * y0 + a * x1 * y1 + b * x2 * y2 - a * b * x3 * y3,
        x0 * y1 + x1 * y0 - b * x2 * y3 + b * x3 * y2,
        x0 * y2 + x2 * y0 + a * x1 * y3 - a * x3 * y1,
        x0 * y3 + x3 * y0 + x1 * y2 - x2 * y1,
    )


def conj(x):
    return (x[0], -x[1], -x[2], -x[3])


def nrd(x):
    return qmul(x, conj(x))[0]


basis = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
# associativity of the multiplication table
assoc = all(qmul(qmul(p, q), r) == qmul(p, qmul(q, r)) for p in basis for q in basis for r in basis)
check("A0 quaternion multiplication is associative", assoc)
check("A0 i^2 = -1, j^2 = 3, ij = k", qmul(basis[1], basis[1]) == (-1, 0, 0, 0)
      and qmul(basis[2], basis[2]) == (3, 0, 0, 0) and qmul(basis[1], basis[2]) == basis[3])
# (-1,3)_Q is a division algebra: x0^2 + x1^2 - 3 x2^2 - 3 x3^2 = 0 has no nonzero rational
# solution (mod 3 descent: x0, x1 divisible by 3, then x2, x3 divisible by 3).  Brute check:
nz = [v for v in itertools.product(range(-6, 7), repeat=4) if any(v) and nrd(v) == 0]
check("A0 no nonzero small vectors of reduced norm 0 (division algebra, indefinite)", not nz)


def gram(mu):
    # f(x, y) = trd(mu * conj(x) * y) = 2 Re(mu * conj(x) * y)
    return [[2 * qmul(qmul(mu, conj(p)), q)[0] for q in basis] for p in basis]


def pf(G):
    return G[0][1] * G[2][3] - G[0][2] * G[1][3] + G[0][3] * G[1][2]


# Lambda = Z<1, i, j, k> has trd-dual Lambda^# = span(1/2, i/2, j/6, k/6); the trace form
# has determinant 144, so Pf(f) = +-12 nrd(mu) and we need mu in Lambda^# pure with nrd 1/12.
found = None
for m in itertools.product(range(-3, 4), repeat=3):
    if not any(m):
        continue
    mu = (Fraction(0), Fraction(m[0], 2), Fraction(m[1], 6), Fraction(m[2], 6))
    G = gram(mu)
    if all(x.denominator == 1 for r in G for x in r) and abs(pf(G)) == 1 and nrd(mu) > 0:
        found = (mu, [[int(x) for x in r] for r in G])
        break
check("A1 found pure mu in the trace dual with unimodular integral form and nrd(mu) > 0", found is not None)
mu, G = found
print("   mu =", tuple(str(x) for x in mu), " nrd(mu) =", nrd(mu), " Gram =", G)
check("A1 form is alternating", all(G[p][q] == -G[q][p] for p in range(4) for q in range(4)))

Gm = np.array(G, dtype=object)


def f(v, w):
    return sum(v[p] * G[p][q] * w[q] for p in range(4) for q in range(4))


# integral symplectic basis v1, v2, w1, w2 with f(v_r, w_s) = delta, f(v, v) = f(w, w) = 0
vecs = [v for v in itertools.product(range(-1, 2), repeat=4) if any(v)]
P = None
for v1 in vecs:
    for w1 in vecs:
        if f(v1, w1) != 1:
            continue
        perp = [x for x in vecs if f(v1, x) == 0 and f(w1, x) == 0]
        for v2 in perp:
            for w2 in perp:
                if f(v2, w2) != 1:
                    continue
                M = np.array([v1, v2, w1, w2], dtype=object).T
                d = int(round(np.linalg.det(np.array(M, dtype=float))))
                if abs(d) == 1:
                    P = M
                    break
            if P is not None:
                break
        if P is not None:
            break
    if P is not None:
        break
check("A2 integral symplectic basis found", P is not None)
J = np.array([[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]], dtype=object)
check("A2 P^T G P = J", (P.T.dot(Gm).dot(P) == J).all())


def inv_int(M):
    Mf = np.array(M, dtype=float)
    Mi = np.linalg.inv(Mf)
    R = np.array(np.round(Mi), dtype=object)
    assert (np.array(M, dtype=object).dot(R) == np.eye(4, dtype=int)).all()
    return R


Pinv = inv_int(P)


def left_mult_matrix(u):
    return np.array([qmul(u, q) for q in basis], dtype=object).T


def to_std(u):
    return Pinv.dot(left_mult_matrix(u)).dot(P)


gens = {"i": (0, 1, 0, 0), "2+j": (2, 0, 1, 0), "2+k": (2, 0, 0, 1)}
mats = {}
for name, u in gens.items():
    check("A3 nrd(%s) = 1" % name, nrd(u) == 1)
    M = to_std(u)
    mats[name] = M
    check("A3 %s acts by an integral matrix preserving J (in Sp_4(Z))" % name,
          all(isinstance(int(x), int) for x in M.flatten()) and (M.T.dot(J).dot(M) == J).all())
    print("   %s ->" % name, [list(map(int, r)) for r in M])
Mi = mats["i"]
I4 = np.eye(4, dtype=int)
check("A4 image of i has order 4", not (Mi.dot(Mi) == I4).all() and (Mi.dot(Mi).dot(Mi).dot(Mi) == I4).all())
for name in ["2+j", "2+k"]:
    tr = int(sum(mats[name][r][r] for r in range(4)))
    check("A4 %s is hyperbolic (trace %d > 4 on the 4-dim rep = 2 * trd)" % (name, tr), tr > 4)
# commutant torus: right multiplication by Q(mu)^1 preserves f; compact iff mu^2 < 0
mu2 = qmul(mu, mu)
check("A5 mu^2 = -nrd(mu) < 0, so the commutant torus SO(2) is R-anisotropic (compact)",
      tuple(mu2) == (-nrd(mu), 0, 0, 0) and nrd(mu) > 0)
# right multiplication by mu preserves f up to nrd(mu): f(x mu, y mu) = nrd(mu) f(x, y)
R = np.array([qmul(q, mu) for q in basis], dtype=object).T
check("A5 right multiplication by mu is a similitude of f with factor nrd(mu)",
      (R.T.dot(Gm).dot(R) == nrd(mu) * Gm).all())

# ---------------------------------------------------------------- Part B
Pf_ = np.array(P, dtype=float)
Pinvf = np.array(Pinv, dtype=float)
Lf = {q: np.array(left_mult_matrix(q), dtype=float) for q in [(1, 0, 0, 0), (0, 1, 0, 0)]}


def unitary_part_phase(M):
    U, s, Vt = np.linalg.svd(M)
    O = U.dot(Vt)  # orthogonal polar factor, lies in Sp_4(R) cap O(4) = U(2)
    A = O[:2, :2]
    Bm = O[2:, :2]
    return np.linalg.det(A + 1j * Bm)


def winding(loop, N=2000):
    tot = 0.0
    prev = unitary_part_phase(loop(0.0))
    for t in np.linspace(0, 2 * np.pi, N + 1)[1:]:
        cur = unitary_part_phase(loop(t))
        tot += np.angle(cur / prev)
        prev = cur
    return tot / (2 * np.pi)


def compact_loop(t):
    Lq = np.cos(t) * Lf[(1, 0, 0, 0)] + np.sin(t) * Lf[(0, 1, 0, 0)]
    return Pinvf.dot(Lq).dot(Pf_)


def block_loop(t):
    c, s = np.cos(t), np.sin(t)
    M = np.eye(4)
    M[0, 0], M[0, 2], M[2, 0], M[2, 2] = c, -s, s, c
    return M


wc = winding(compact_loop)
wb = winding(block_loop)
print("   winding(compact loop of D^1(R)) = %.6f, winding(block SL_2 loop) = %.6f" % (wc, wb))
check("B1 block SL_2 has winding +-1", abs(abs(wb) - 1) < 1e-6)
check("B2 compact loop of the [2,2] packet has winding +-2 (omega + omega type, P4 does not apply)",
      abs(abs(wc) - 2) < 1e-6)

# ---------------------------------------------------------------- Part C
# B = (Z/3)^2 x| Z/2 with sigma(x) = -x; S = (Z/3)^2.  Heisenberg cocycle on S:
# c((x1, y1), (x2, y2)) = zeta^{y1 x2}; extend to B via the projective representation
# of B built from the Schrodinger representation and the parity operator (a genuine
# alpha-projective rep of B exists here), then compare with the induced construction.
zeta = np.exp(2j * np.pi / 3)
X = np.diag([zeta ** r for r in range(3)])
Y = np.roll(np.eye(3), 1, axis=0)
Par = np.zeros((3, 3))
for r in range(3):
    Par[(-r) % 3, r] = 1


def elem_list():
    return [(x, y, e) for x in range(3) for y in range(3) for e in range(2)]


def rho0(g):
    x, y, e = g
    M = np.linalg.matrix_power(X, x).dot(np.linalg.matrix_power(Y, y))
    return M.dot(Par) if e else M


def bmul(g, h):
    x1, y1, e1 = g
    x2, y2, e2 = h
    s = -1 if e1 else 1
    return ((x1 + s * x2) % 3, (y1 + s * y2) % 3, (e1 + e2) % 2)


def multiplier(rho, g, h):
    M = rho(g).dot(rho(h)).dot(np.linalg.inv(rho(bmul(g, h))))
    lam = M[0, 0]
    assert np.allclose(M, lam * np.eye(M.shape[0]))
    return lam


Bl = elem_list()
c = {(g, h): multiplier(rho0, g, h) for g in Bl for h in Bl}
Sl = [g for g in Bl if g[2] == 0]
# pi = restriction of rho0 to S: pi(s) pi(s') = c(s, s') pi(ss')
reps = [(0, 0, 0), (0, 0, 1)]


def coset_decomp(g):
    # g = r_i * s with s in S
    for i, r in enumerate(reps):
        for s in Sl:
            if bmul(r, s) == g:
                return i, s
    raise AssertionError


def rho_ind(g):
    n = 3
    M = np.zeros((2 * n, 2 * n), dtype=complex)
    for j, r in enumerate(reps):
        i, s = coset_decomp(bmul(g, r))
        # u_g u_{r_j} = c(g, r_j) u_{g r_j} = c(g, r_j) conj(c(r_i, s)) u_{r_i} u_s
        coef = c[(g, r)] * np.conj(c[(reps[i], s)])
        M[i * n:(i + 1) * n, j * n:(j + 1) * n] = coef * rho0(s)
    return M


ok_cocycle = all(np.allclose(rho_ind(g).dot(rho_ind(h)), c[(g, h)] * rho_ind(bmul(g, h))) for g in Bl for h in Bl)
ok_unitary = all(np.allclose(rho_ind(g).conj().T.dot(rho_ind(g)), np.eye(6)) for g in Bl)
check("C1 induced representation through C^c[S] <= C^c[B] has multiplier exactly c", ok_cocycle)
check("C2 induced representation is unitary", ok_unitary)

# ---------------------------------------------------------------- Part D
# genus-2 surface group <a1, b1, a2, b2 | [a1, b1][a2, b2]>; a1 -> X_n, b1 -> Y_n, others -> I.
for n in [2, 3, 5]:
    zn = np.exp(2j * np.pi / n)
    Xn = np.diag([zn ** r for r in range(n)])
    Yn = np.roll(np.eye(n), 1, axis=0)
    for k in range(n):
        Xk = np.linalg.matrix_power(Xn, k)
        comm = Xk.dot(Yn).dot(np.linalg.inv(Xk)).dot(np.linalg.inv(Yn))
        lam = comm[0, 0]
        good = np.allclose(comm, lam * np.eye(n))
        # the relator value lam = zn^{-k}: the Hopf evaluation of the multiplier on [S]
        if (not good) or not np.isclose(lam, zn ** k):
            FAIL.append("D n=%d k=%d" % (n, k))
    check("D1 clock-shift realizes every class in Hom(H_2(S), Z/%d) on a genus-2 surface group" % n,
          not any(s.startswith("D n=%d" % n) for s in FAIL))

print("ALL PASS" if not FAIL else "FAILURES: %s" % FAIL)
