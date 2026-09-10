#!/usr/bin/env python3
"""sp-design deliverable 2/4: local degrees of Psi_k at the k preimages of -e_1,
computed in CANONICAL bases so that no QR orientation artifact enters.

At q_j = zeta_j e_1 (zeta_j^k = -1) the real tangent space of the equator
S^{2n} = {|x| = 1, Re x_n = 0} is  R.(i q_j) (+) V,  V = the "rest" real space
{ (0, x_1, ..., x_{n-1}, i s) }.  Basis: [ i q_j ,  standard basis of V ].
At the target -e_1 the same recipe gives [ i(-e_1), standard basis of V ].

Claim: in these bases  d Psi_k = diag(k, 1, ..., 1)  at EVERY q_j.  So every local
degree is +1 and deg(psi_k) = +k, with no sign to compute.

Also: the full section  S(u, x) = (1-tau) e_1 + tau Psi_k(x),  tau = (1+u)/2,
read in the canonical bases of R x T_{q_j} on the source and of the real
2(n+1)-space on the target, has the SAME matrix for every j after transporting
the source basis by rho^j.  That is the linear-algebra shadow of the note's
"every local contribution is literally equal".
"""
import cmath, math
import numpy as np

rng = np.random.default_rng(11)


def Psi(x, k):
    x = np.asarray(x, dtype=complex).copy()
    z = x[0]; a = abs(z)
    x[0] = 0.0 if a == 0.0 else z ** k / a ** (k - 1)
    return x


def toR(z):
    return np.concatenate([np.real(z), np.imag(z)])


def canonical_basis(p, n1):
    """p on the circle {|x_0| = 1, rest = 0}; returns the real 2n x 2(n+1) basis
    matrix (columns) of T_p(S^{2n})."""
    cols = [toR(1j * p)]
    for i in range(1, n1 - 1):            # full complex coordinates x_1..x_{n-1}
        e = np.zeros(n1, dtype=complex); e[i] = 1.0
        cols.append(toR(e))
        cols.append(toR(1j * e))
    e = np.zeros(n1, dtype=complex); e[n1 - 1] = 1j    # only Im x_n survives
    cols.append(toR(e))
    return np.array(cols).T


def numeric_dPsi(p, k, n1, Bs, Bt):
    eps = 1e-6
    m = Bs.shape[1]
    J = np.zeros((Bt.shape[1], m))
    for i in range(m):
        v = Bs[:, i]
        vc = v[:n1] + 1j * v[n1:]
        xp = p + eps * vc; xm = p - eps * vc
        for z in (xp, xm):
            z[n1 - 1] = 1j * z[n1 - 1].imag
        xp /= np.linalg.norm(xp); xm /= np.linalg.norm(xm)
        J[:, i] = Bt.T @ ((toR(Psi(xp, k)) - toR(Psi(xm, k))) / (2 * eps))
    return J


def section(u, x, k, n1, e1):
    tau = (1 + u) / 2
    return (1 - tau) * e1 + tau * Psi(x, k)


def numeric_dSection(p, k, n1, e1, Bs):
    eps = 1e-6
    cols = [(toR(section(eps, p, k, n1, e1)) - toR(section(-eps, p, k, n1, e1))) / (2 * eps)]
    for i in range(Bs.shape[1]):
        v = Bs[:, i]; vc = v[:n1] + 1j * v[n1:]
        xp = p + eps * vc; xm = p - eps * vc
        for z in (xp, xm):
            z[n1 - 1] = 1j * z[n1 - 1].imag
        xp /= np.linalg.norm(xp); xm /= np.linalg.norm(xm)
        cols.append((toR(section(0.0, xp, k, n1, e1)) - toR(section(0.0, xm, k, n1, e1))) / (2 * eps))
    return np.array(cols).T


print("== dPsi_k in canonical bases: expect diag(k,1,...,1) at every preimage ==")
for n in (2, 3, 4):
    n1 = n + 1
    e1 = np.zeros(n1, dtype=complex); e1[0] = 1.0
    for k in range(1, 8):
        Bt = canonical_basis(-e1, n1)
        rows = []
        for j in range(k):
            q = np.zeros(n1, dtype=complex)
            q[0] = cmath.exp(1j * math.pi * (2 * j + 1) / k)
            Bs = canonical_basis(q, n1)
            J = numeric_dPsi(q, k, n1, Bs, Bt)
            want = np.diag([float(k)] + [1.0] * (2 * n - 1))
            rows.append((float(np.max(np.abs(J - want))), float(np.linalg.det(J))))
        maxerr = max(r[0] for r in rows)
        dets = [round(r[1], 6) for r in rows]
        print(f"   n={n} k={k}: max|J - diag(k,1..1)| = {maxerr:.2e}   dets = {dets}")

print()
print("== d(section) at the k zeros, source basis transported by rho^j: expect all equal ==")
for n in (2, 3):
    n1 = n + 1
    e1 = np.zeros(n1, dtype=complex); e1[0] = 1.0
    for k in range(1, 7):
        mats = []
        for j in range(k):
            q = np.zeros(n1, dtype=complex)
            q[0] = cmath.exp(1j * math.pi * (2 * j + 1) / k)
            Bs = canonical_basis(q, n1)
            mats.append(numeric_dSection(q, k, n1, e1, Bs))
        diffs = [float(np.max(np.abs(m - mats[0]))) for m in mats]
        # rank / smallest singular value
        sv = min(float(np.linalg.svd(m, compute_uv=False)[-1]) for m in mats)
        print(f"   n={n} k={k}: max spread over the k zeros = {max(diffs):.2e}   min sv = {sv:.4f}"
              f"   rank = {np.linalg.matrix_rank(mats[0], tol=1e-6)} (want {2*n+1})")
