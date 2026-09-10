#!/usr/bin/env python3
"""Model test for sp-design deliverable 2: the k-fold map Psi_k.

Psi_k : S^{2n+1} -> S^{2n+1},  x = (x_0, x_1, ..., x_n) in C^{n+1},
    Psi_k(x) = ( x_0^k / |x_0|^{k-1}, x_1, ..., x_n )     (0 -> 0)

Claims tested:
  A. Psi_k maps the unit sphere to itself and preserves Re(x_n) (so it is the
     suspension of its restriction to the equator {Re x_n = 0}).
  B. rho-invariance: Psi_k(rho x) = Psi_k(x), rho = diag(w,1,...,1), w = e^{2 pi i /k}.
  C. Psi_k^{-1}(-e_1) = { zeta e_1 : zeta^k = -1 }: exactly k points, one free
     rho-orbit, all on the equator.
  D. At each such point Psi_k is a local diffeomorphism of the equator S^{2n},
     with an invertible real Jacobian, and all k local degrees have the SAME sign
     (in fact +1), so deg(psi_k) = k.
  E. The transported section with a = e_1, b = Psi_k o x, c = tautological column
     vanishes exactly at {south pole} x {k points} x {base point of Y}, and its
     real Jacobian at each zero is invertible.
  F. The chart at -e_1 (coordinate-free form: L w - sqrt(1-|w|^2) a) has the
     claimed derivative and is a linear iso.
  G. Eckmann-Hilton bookkeeping: for based loops in a matrix group,
       prod_{j=1}^{k} gamma(clamp01(k t - (j-1)))  ==  gamma(frac(k t)),
     and the interpolation H_s(t) = prod_j gamma(clamp01(((1-s)+s k) t - s(j-1)))
     is a homotopy from gamma(t)^k (s=0) to the k-fold concatenation (s=1),
     through loops based at the identity.
  H. deg via signed preimage count of a random regular value of psi_k on S^{2n}.
"""

import itertools
import math
import cmath
import random

import numpy as np

rng = np.random.default_rng(20260910)


# ---------------------------------------------------------------- Psi_k

def Psi(x, k):
    """x: complex vector of length n+1."""
    x = np.asarray(x, dtype=complex)
    y = x.copy()
    z = x[0]
    a = abs(z)
    if a == 0.0:
        y[0] = 0.0
    else:
        y[0] = z ** k / a ** (k - 1)
    return y


def rho(x, k, j=1):
    x = np.asarray(x, dtype=complex).copy()
    x[0] *= cmath.exp(2j * math.pi * j / k)
    return x


def rand_sphere(n1):
    """random point of S^{2n+1} in C^{n+1}, n1 = n+1"""
    v = rng.normal(size=2 * n1)
    v /= np.linalg.norm(v)
    return v[:n1] + 1j * v[n1:]


def rand_equator(n1):
    """random point of the equator {Re x_n = 0}"""
    while True:
        x = rand_sphere(n1)
        x[n1 - 1] = 1j * x[n1 - 1].imag
        nrm = np.linalg.norm(x)
        if nrm > 1e-9:
            return x / nrm


# ------------------------------------------------------- A, B: basics

def test_A_B(nmax=4, kmax=7, trials=400):
    bad = []
    for n in range(2, nmax + 1):
        n1 = n + 1
        for k in range(1, kmax + 1):
            for _ in range(trials):
                x = rand_sphere(n1)
                y = Psi(x, k)
                if abs(np.linalg.norm(y) - 1.0) > 1e-10:
                    bad.append(("norm", n, k, np.linalg.norm(y)))
                if abs(y[n1 - 1].real - x[n1 - 1].real) > 1e-12:
                    bad.append(("height", n, k))
                for j in range(k):
                    if np.max(np.abs(Psi(rho(x, k, j), k) - y)) > 1e-10:
                        bad.append(("rho", n, k, j))
            # x_0 = 0 branch
            x = rand_sphere(n1)
            x[0] = 0.0
            x /= np.linalg.norm(x)
            if np.max(np.abs(Psi(x, k) - x)) > 1e-12:
                bad.append(("fixedset", n, k))
    return bad


# ------------------------------------------------- C: the k preimages

def preimages_of_neg_e1(n, k):
    n1 = n + 1
    pts = []
    for j in range(k):
        zeta = cmath.exp(1j * math.pi * (2 * j + 1) / k)
        p = np.zeros(n1, dtype=complex)
        p[0] = zeta
        pts.append(p)
    return pts


def test_C(nmax=4, kmax=8, grid=200000):
    """check the closed form, that they are a free rho-orbit, that they are on the
    equator, that none is on the wall {arg x_0 = 0}, and (by dense sampling of the
    equator) that no other point of the equator maps near -e_1."""
    out = {}
    for n in range(2, nmax + 1):
        n1 = n + 1
        for k in range(1, kmax + 1):
            e1 = np.zeros(n1, dtype=complex); e1[0] = 1.0
            pts = preimages_of_neg_e1(n, k)
            errs = [np.max(np.abs(Psi(p, k) + e1)) for p in pts]
            # free rho-orbit of pts[0]
            orb = [rho(pts[0], k, j) for j in range(k)]
            match = all(min(np.max(np.abs(o - p)) for p in pts) < 1e-12 for o in orb)
            distinct = min(np.max(np.abs(a - b)) for a, b in itertools.combinations(pts, 2)) if k > 1 else 1.0
            oneq = all(abs(p[n1 - 1].real) < 1e-15 for p in pts)
            offwall = all(abs(p[0].imag) > 1e-12 or p[0].real < 0 for p in pts)
            # no other preimage: sample the equator, keep the closest ones
            best = []
            for _ in range(grid // 50):
                x = rand_equator(n1)
                d = np.max(np.abs(Psi(x, k) + e1))
                best.append((d, x))
            best.sort(key=lambda t: t[0])
            # refine the 20 best by local descent; each must land on one of pts
            stray = 0
            for d, x in best[:20]:
                y = x.copy()
                for _ in range(300):
                    g = Psi(y, k) + e1
                    # crude gradient step in the ambient, then reproject
                    eps = 1e-5
                    grad = np.zeros_like(y)
                    for i in range(n1):
                        for part in (1.0, 1j):
                            yy = y.copy(); yy[i] += eps * part
                            yy[n1 - 1] = 1j * yy[n1 - 1].imag
                            yy /= np.linalg.norm(yy)
                            gg = Psi(yy, k) + e1
                            grad[i] += part * (np.sum(np.abs(gg) ** 2) - np.sum(np.abs(g) ** 2)) / eps
                    y = y - 0.05 * grad.conj()
                    y[n1 - 1] = 1j * y[n1 - 1].imag
                    nn = np.linalg.norm(y)
                    if nn < 1e-9:
                        break
                    y /= nn
                if np.max(np.abs(Psi(y, k) + e1)) < 1e-4:
                    if min(np.max(np.abs(y - p)) for p in pts) > 1e-2:
                        stray += 1
            out[(n, k)] = dict(maxerr=max(errs), free_orbit=match, distinct=float(distinct),
                               on_equator=oneq, off_wall=offwall, strays=stray)
    return out


# ------------------------------------- D: local degree at each preimage

def equator_tangent_basis(p, n1):
    """real orthonormal basis of T_p(S^{2n}) inside the real 2(n+1)-space,
    S^{2n} = {|x|=1, Re x_n = 0}."""
    def toR(z):
        return np.concatenate([z.real, z.imag])
    def toC(v):
        return v[:n1] + 1j * v[n1:]
    N = 2 * n1
    cons = [toR(p)]                       # radial
    en = np.zeros(n1, dtype=complex); en[n1 - 1] = 1.0
    cons.append(toR(en))                  # Re x_n direction
    A = np.array(cons)
    # orthonormal complement
    Q, _ = np.linalg.qr(A.T, mode='complete')
    B = Q[:, len(cons):]                  # N x (N-2) = 2n+... ; dim S^{2n} = 2n
    return B, toR, toC


def local_jacobian_sign(p, k, n):
    n1 = n + 1
    Bs, toR, toC = equator_tangent_basis(p, n1)
    q = Psi(p, k)
    Bt, _, _ = equator_tangent_basis(q, n1)
    eps = 1e-6
    m = Bs.shape[1]
    J = np.zeros((Bt.shape[1], m))
    for i in range(m):
        v = toC(Bs[:, i])
        xp = p + eps * v
        xm = p - eps * v
        for x in (xp, xm):
            x[n1 - 1] = 1j * x[n1 - 1].imag
        xp /= np.linalg.norm(xp); xm /= np.linalg.norm(xm)
        d = (toR(Psi(xp, k)) - toR(Psi(xm, k))) / (2 * eps)
        J[:, i] = Bt.T @ d
    return np.linalg.det(J), J.shape


def test_D(nmax=4, kmax=7):
    out = {}
    for n in range(2, nmax + 1):
        for k in range(1, kmax + 1):
            pts = preimages_of_neg_e1(n, k)
            dets = []
            for p in pts:
                d, shape = local_jacobian_sign(p, k, n)
                dets.append(d)
            # orientation of the target basis is arbitrary but FIXED (same q for all p),
            # and the source bases are computed by the same QR recipe from p; to compare
            # signs meaningfully we transport by rho, see test_D_rho below.
            out[(n, k)] = dict(dets=[float(x) for x in dets],
                               signs=[int(np.sign(x)) for x in dets],
                               all_same=len(set(int(np.sign(x)) for x in dets)) == 1)
    return out


def test_D_rho(nmax=4, kmax=7):
    """the invariant statement: near rho^j q_0, Psi_k = (Psi_k near q_0) o rho^{-j}.
    Check it as an identity of maps on a neighbourhood."""
    bad = []
    for n in range(2, nmax + 1):
        n1 = n + 1
        for k in range(1, kmax + 1):
            q0 = preimages_of_neg_e1(n, k)[0]
            for j in range(k):
                qj = rho(q0, k, j)
                for _ in range(200):
                    v = rand_equator(n1)
                    x = qj + 0.01 * v
                    x[n1 - 1] = 1j * x[n1 - 1].imag
                    x /= np.linalg.norm(x)
                    lhs = Psi(x, k)
                    rhs = Psi(rho(x, k, -j % k), k)
                    if np.max(np.abs(lhs - rhs)) > 1e-10:
                        bad.append((n, k, j))
                        break
    return bad


# ---------------------------------------- H: degree by signed count

def test_H_degree(nmax=3, kmax=6, trials=6):
    """pick a random regular value y of psi_k on the equator, find all preimages in
    closed form (possible for this map), sum the local signs, compare with k."""
    out = {}
    for n in range(2, nmax + 1):
        n1 = n + 1
        for k in range(1, kmax + 1):
            tot = []
            for _ in range(trials):
                y = rand_equator(n1)
                if abs(y[0]) < 1e-3:
                    continue
                # preimages: x_0 with x_0^k/|x_0|^{k-1} = y_0  =>  |x_0| = |y_0|,
                # arg x_0 = (arg y_0 + 2 pi j)/k ; other coords = y's
                r = abs(y[0]); th = cmath.phase(y[0])
                pre = []
                for j in range(k):
                    x = y.copy()
                    x[0] = r * cmath.exp(1j * (th + 2 * math.pi * j) / k)
                    pre.append(x)
                # check
                assert all(np.max(np.abs(Psi(x, k) - y)) < 1e-9 for x in pre)
                signs = []
                Bt, toR, toC = equator_tangent_basis(y, n1)
                for x in pre:
                    Bs, _, _ = equator_tangent_basis(x, n1)
                    eps = 1e-6
                    m = Bs.shape[1]
                    J = np.zeros((Bt.shape[1], m))
                    for i in range(m):
                        v = toC(Bs[:, i])
                        xp = x + eps * v; xm = x - eps * v
                        for z in (xp, xm):
                            z[n1 - 1] = 1j * z[n1 - 1].imag
                        xp /= np.linalg.norm(xp); xm /= np.linalg.norm(xm)
                        J[:, i] = Bt.T @ ((toR(Psi(xp, k)) - toR(Psi(xm, k))) / (2 * eps))
                    signs.append(int(np.sign(np.linalg.det(J))))
                # the source bases from QR carry an arbitrary orientation; fix it by
                # comparing each source basis with the rho-transport of the first
                # (rho is orientation preserving, being in the identity component)
                B0, _, _ = equator_tangent_basis(pre[0], n1)
                fixed = [signs[0]]
                for idx in range(1, len(pre)):
                    # transport B0 by the rotation taking pre[0] to pre[idx]
                    ang = cmath.phase(pre[idx][0]) - cmath.phase(pre[0][0])
                    M = np.eye(n1, dtype=complex); M[0, 0] = cmath.exp(1j * ang)
                    Bt0 = np.array([toR(M @ toC(B0[:, i])) for i in range(B0.shape[1])]).T
                    Bi, _, _ = equator_tangent_basis(pre[idx], n1)
                    C = Bi.T @ Bt0
                    fixed.append(signs[idx] * int(np.sign(np.linalg.det(C))))
                tot.append(sum(fixed))
            out[(n, k)] = tot
    return out


# -------------------------------------- E: the section and its zeros

def section_trivial_block(u, x, k, n1, e1):
    """(1-tau) a + tau b,  a = e1, b = Psi_k(x), tau = (1+u)/2, u the circle horiz coord
       on the southern half."""
    tau = (1.0 + u) / 2.0
    return (1 - tau) * e1 + tau * Psi(x, k)


def test_E(nmax=3, kmax=6, trials=200000):
    out = {}
    for n in range(2, nmax + 1):
        n1 = n + 1
        e1 = np.zeros(n1, dtype=complex); e1[0] = 1.0
        for k in range(1, kmax + 1):
            pts = preimages_of_neg_e1(n, k)
            # zeros: u = 0 and x in pts
            errs = [np.max(np.abs(section_trivial_block(0.0, p, k, n1, e1))) for p in pts]
            # sampling: the minimum of |section| away from the k zeros must be bounded away
            worst = 1e9
            for _ in range(trials // 100):
                u = rng.uniform(-1, 1)
                x = rand_equator(n1)
                d = min(abs(u) + np.max(np.abs(x - p)) for p in pts)
                if d < 0.05:
                    continue
                worst = min(worst, np.max(np.abs(section_trivial_block(u, x, k, n1, e1))))
            out[(n, k)] = dict(zero_err=max(errs), min_away=float(worst))
    return out


def test_E_jac(nmax=3, kmax=6):
    """real Jacobian of (u, x) -> (1-tau) e1 + tau Psi_k(x) at each zero,
    source = R (circle) x T_x(S^{2n}) = R^{1+2n}, target = R^{2n+1}
    (the trivial block lands in the real 2(n+1) space but the section's value is
    constrained: |value| small; we take the full ambient and check rank)."""
    out = {}
    for n in range(2, nmax + 1):
        n1 = n + 1
        e1 = np.zeros(n1, dtype=complex); e1[0] = 1.0
        for k in range(1, kmax + 1):
            pts = preimages_of_neg_e1(n, k)
            rks, dets = [], []
            for p in pts:
                Bs, toR, toC = equator_tangent_basis(p, n1)
                m = Bs.shape[1]
                cols = []
                eps = 1e-6
                # circle direction
                cols.append((toR(section_trivial_block(eps, p, k, n1, e1))
                             - toR(section_trivial_block(-eps, p, k, n1, e1))) / (2 * eps))
                for i in range(m):
                    v = toC(Bs[:, i])
                    xp = p + eps * v; xm = p - eps * v
                    for z in (xp, xm):
                        z[n1 - 1] = 1j * z[n1 - 1].imag
                    xp /= np.linalg.norm(xp); xm /= np.linalg.norm(xm)
                    cols.append((toR(section_trivial_block(0.0, xp, k, n1, e1))
                                 - toR(section_trivial_block(0.0, xm, k, n1, e1))) / (2 * eps))
                J = np.array(cols).T          # 2(n+1) x (1+2n)
                rks.append(int(np.linalg.matrix_rank(J, tol=1e-6)))
                s = np.linalg.svd(J, compute_uv=False)
                dets.append(float(s[-1]))
            out[(n, k)] = dict(ranks=rks, want=1 + 2 * n, min_sv=min(dets))
    return out


# ------------------------------- F: the chart at -a, coordinate-free

def test_F(nmax=4, trials=300):
    """chart_a(w) = L w - sqrt(1-|w|^2) a ; derivative of (1-tau)a + tau chart_a(w)
    at (w,u) = 0 is (dw, du) -> (1/2) L dw - du a, and it is invertible."""
    bad = []
    for n in range(2, nmax + 1):
        n1 = n + 1
        N = 2 * n1
        for _ in range(trials):
            # random unit a with Re a_n = 0
            a = rand_equator(n1)
            def toR(z): return np.concatenate([z.real, z.imag])
            def toC(v): return v[:n1] + 1j * v[n1:]
            aR = toR(a)
            Q, _ = np.linalg.qr(aR.reshape(-1, 1), mode='complete')
            L = Q[:, 1:]                       # N x (N-1), image = a^perp_R
            def chart(w):
                s = math.sqrt(max(0.0, 1 - float(w @ w)))
                return L @ w - s * aR
            # numeric derivative of F(w,u) = (1-tau) a + tau chart(w), tau=(1+u)/2
            def F(w, u):
                tau = (1 + u) / 2
                return (1 - tau) * aR + tau * chart(w)
            eps = 1e-6
            cols = []
            for i in range(N - 1):
                w = np.zeros(N - 1); w[i] = eps
                cols.append((F(w, 0.0) - F(-w, 0.0)) / (2 * eps))
            cols.append((F(np.zeros(N - 1), eps) - F(np.zeros(N - 1), -eps)) / (2 * eps))
            J = np.array(cols).T
            pred = np.concatenate([0.5 * L, -aR.reshape(-1, 1)], axis=1)
            if np.max(np.abs(J - pred)) > 1e-5:
                bad.append(("formula", n, float(np.max(np.abs(J - pred)))))
            if abs(np.linalg.det(J)) < 1e-9:
                bad.append(("singular", n, float(np.linalg.det(J))))
            if np.max(np.abs(chart(np.zeros(N - 1)) + aR)) > 1e-12:
                bad.append(("chart0", n))
    return bad


# ------------------------------ G: Eckmann-Hilton bookkeeping

def clamp01(t):
    return min(1.0, max(0.0, t))


def test_G(kmax=6, trials=200, dim=3):
    """gamma: [0,1] -> U(dim) with gamma(0)=gamma(1)=I.
    (a) prod_j gamma(clamp01(k t - (j-1))) == gamma(frac(k t))
    (b) H_s continuous in s, H_0 = gamma^k, H_1 = the concatenation, all based at I."""
    def gamma(t, A):
        # a based loop: exp(2 pi i t A) with A Hermitian integer-spectrum
        return np.array(scipy_expm(2j * math.pi * t * A))
    bad = []
    for _ in range(trials):
        # A Hermitian with integer eigenvalues -> exp(2 pi i t A) is a based loop
        U = np.linalg.qr(rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim)))[0]
        d = rng.integers(-2, 3, size=dim)
        A = U @ np.diag(d.astype(float)) @ U.conj().T
        for k in range(1, kmax + 1):
            for t in rng.uniform(0, 1, size=25):
                prod = np.eye(dim, dtype=complex)
                for j in range(1, k + 1):
                    prod = prod @ gamma(clamp01(k * t - (j - 1)), A)
                frac = (k * t) % 1.0
                if abs(k * t - round(k * t)) < 1e-12:
                    continue
                if np.max(np.abs(prod - gamma(frac, A))) > 1e-8:
                    bad.append(("concat", k, float(t), float(np.max(np.abs(prod - gamma(frac, A))))))
            # endpoints of the interpolation
            for s in (0.0, 1.0):
                for t in rng.uniform(0, 1, size=10):
                    H = np.eye(dim, dtype=complex)
                    for j in range(1, k + 1):
                        H = H @ gamma(clamp01(((1 - s) + s * k) * t - s * (j - 1)), A)
                    if s == 0.0:
                        want = np.linalg.matrix_power(gamma(t, A), k)
                    else:
                        want = gamma((k * t) % 1.0 if abs(k * t - round(k * t)) > 1e-12 else 0.0, A)
                        if abs(k * t - round(k * t)) < 1e-12:
                            continue
                    if np.max(np.abs(H - want)) > 1e-8:
                        bad.append(("interp", k, s, float(t)))
            # based at I at t=0 and t=1 for every s
            for s in rng.uniform(0, 1, size=5):
                for t in (0.0, 1.0):
                    H = np.eye(dim, dtype=complex)
                    for j in range(1, k + 1):
                        H = H @ gamma(clamp01(((1 - s) + s * k) * t - s * (j - 1)), A)
                    if np.max(np.abs(H - np.eye(dim))) > 1e-9:
                        bad.append(("based", k, float(s), t))
    return bad


def scipy_expm(M):
    w, V = np.linalg.eig(M)
    return V @ np.diag(np.exp(w)) @ np.linalg.inv(V)


# ------------------------------------------------------------- main

if __name__ == "__main__":
    print("== A,B: sphere, height, rho-invariance ==")
    bad = test_A_B()
    print("   violations:", len(bad), bad[:5])

    print("== C: the k preimages of -e_1 ==")
    for key, v in sorted(test_C(nmax=3, kmax=6, grid=60000).items()):
        print("   n,k =", key, v)

    print("== D: local jacobians at the preimages ==")
    for key, v in sorted(test_D(nmax=3, kmax=6).items()):
        print("   n,k =", key, "signs", v["signs"], "all_same", v["all_same"])

    print("== D(rho): Psi_k near rho^j q0 equals (Psi_k near q0) o rho^{-j} ==")
    print("   violations:", test_D_rho(nmax=3, kmax=6))

    print("== H: degree by signed preimage count ==")
    for key, v in sorted(test_H_degree(nmax=3, kmax=5).items()):
        print("   n,k =", key, "signed counts", v)

    print("== E: the section's zero set ==")
    for key, v in sorted(test_E(nmax=3, kmax=5).items()):
        print("   n,k =", key, v)

    print("== E(jac): rank of the section's derivative at each zero ==")
    for key, v in sorted(test_E_jac(nmax=3, kmax=5).items()):
        print("   n,k =", key, v)

    print("== F: the coordinate-free chart at -a ==")
    print("   violations:", test_F(nmax=4, trials=60)[:5])

    print("== G: Eckmann-Hilton bookkeeping ==")
    print("   violations:", test_G(kmax=5, trials=30)[:5])
