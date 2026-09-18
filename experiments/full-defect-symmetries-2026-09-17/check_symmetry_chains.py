"""Numerical sanity check for fg-mf-group-with-full-compression-defect.

Checks, on random inputs in U(2d):
 (1) every v in SU(2d) is a product of four trace-zero symmetries
     (via the cycle pairing of eigenvalues and S1*S2 = diag(D, D^-1));
 (2) any two trace-zero symmetries E, R are joined by a chain
     E = P0, P1, P2, P3, P4 = R of trace-zero symmetries with
     (P_i P_(i+1))^3 = 1, built block by block on the Bloch sphere;
 (3) the D3 identity y = (xy) x (xy)^-1 for such consecutive pairs.
Run: python3 check_symmetry_chains.py
"""
import numpy as np

rng = np.random.default_rng(20260918)
SX = np.array([[0, 1], [1, 0]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
SZ = np.array([[1, 0], [0, -1]], dtype=complex)


def haar(n):
    z = (rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / abs(np.diag(r)))


def is_balanced_symmetry(s, tol=1e-9):
    n = s.shape[0]
    return (np.allclose(s, s.conj().T, atol=tol)
            and np.allclose(s @ s, np.eye(n), atol=tol)
            and abs(np.trace(s)) < tol)


def four_symmetries(v):
    """Return S1..S4, trace-zero symmetries with v = S1 S2 S3 S4 (det v = 1)."""
    n = v.shape[0]
    d = n // 2
    # v is normal: Schur form gives v = W diag(lam) W^*
    from scipy.linalg import schur
    t, w = schur(v, output="complex")
    lam = np.diag(t)
    pref = np.cumprod(lam)          # pref[j] = lam_1...lam_(j+1)
    a1 = np.empty(n, dtype=complex)  # first factor, pairs (0,1),(2,3),...
    a2 = np.empty(n, dtype=complex)  # second factor, pairs (1,2),...,(n-1,0)
    for k in range(d):
        alpha = pref[2 * k]          # lam_1 ... lam_(2k+1)
        a1[2 * k], a1[2 * k + 1] = alpha, 1 / alpha
    for k in range(d):
        beta = pref[2 * k + 1]       # lam_1 ... lam_(2k+2)
        a2[2 * k + 1] = beta
        a2[(2 * k + 2) % n] = 1 / beta
    assert np.allclose(a1 * a2, lam)
    out = []
    for pairs, diag in (([(2 * k, 2 * k + 1) for k in range(d)], a1),
                        ([(2 * k + 1, (2 * k + 2) % n) for k in range(d)], a2)):
        s1 = np.zeros((n, n), dtype=complex)
        s2 = np.zeros((n, n), dtype=complex)
        for p, q in pairs:
            mu = diag[p]
            s1[p, q], s1[q, p] = mu, 1 / mu
            s2[p, q], s2[q, p] = 1, 1
        assert np.allclose(s1 @ s2, np.diag(diag))
        out += [w @ s1 @ w.conj().T, w @ s2 @ w.conj().T]
    return out


def perp(n):
    a = np.array([1.0, 0, 0]) if abs(n[0]) < 0.9 else np.array([0, 1.0, 0])
    w = a - (a @ n) * n
    return w / np.linalg.norm(w)


def mid120(n, m):
    """Unit p with angle(n,p)=angle(m,p)=120 deg; needs angle(n,m)<=120."""
    s = n + m
    u = s / np.linalg.norm(s)
    w = np.cross(n, m)
    w = perp(n) if np.linalg.norm(w) < 1e-12 else w / np.linalg.norm(w)
    alpha = -0.5 / (u @ n)
    return alpha * u + np.sqrt(max(0.0, 1 - alpha ** 2)) * w


def bloch_chain(n, m):
    """Unit vectors n=q0,q1,q2,q3,q4=m, consecutive angles in {0,120 deg}."""
    if n @ m >= -0.5 - 1e-12:
        return [n, mid120(n, m), m, m, m]
    v = m - (n @ m) * n
    v = perp(n) if np.linalg.norm(v) < 1e-12 else v / np.linalg.norm(v)
    p1 = -0.5 * n + np.sqrt(3) / 2 * v
    return [n, p1, mid120(p1, m), m, m]


def blocks(E, R):
    """Orthonormal 2-dim blocks f (n x 2) with f^*Ef = sigma_z, f^*Rf a symmetry."""
    from scipy.linalg import schur
    t, w = schur(E @ R, output="complex")
    out = []
    for j, z in enumerate(np.diag(t)):
        if z.imag > 1e-9:            # generic case: simple spectrum of ER
            x = w[:, j]
            f1 = x + E @ x
            f2 = x - E @ x
            out.append(np.stack([f1 / np.linalg.norm(f1),
                                 f2 / np.linalg.norm(f2)], axis=1))
    return out


def chain(E, R):
    n = E.shape[0]
    fs = blocks(E, R)
    assert len(fs) == n // 2, "degenerate spectrum; use block test"
    P = [np.zeros((n, n), dtype=complex) for _ in range(5)]
    for f in fs:
        r = f.conj().T @ R @ f
        m = np.real([np.trace(r @ S) / 2 for S in (SX, SY, SZ)])
        for i, q in enumerate(bloch_chain(np.array([0, 0, 1.0]), m)):
            P[i] += f @ (q[0] * SX + q[1] * SY + q[2] * SZ) @ f.conj().T
    return P


def main():
    worst = 0.0
    for trial in range(200):
        d = int(rng.integers(1, 7))
        n = 2 * d
        v = haar(n)
        v = v / np.linalg.det(v) ** (1 / n)
        S = four_symmetries(v)
        assert all(is_balanced_symmetry(s) for s in S)
        worst = max(worst, np.abs(S[0] @ S[1] @ S[2] @ S[3] - v).max())
        E = np.diag([-1.0] * d + [1.0] * d).astype(complex)
        for R in S:
            P = chain(E, R)
            assert np.allclose(P[0], E) and np.allclose(P[4], R)
            for i in range(4):
                x, y = P[i], P[i + 1]
                assert is_balanced_symmetry(y)
                xy = x @ y
                worst = max(worst, np.abs(np.linalg.matrix_power(xy, 3) - np.eye(n)).max())
                worst = max(worst, np.abs(xy @ x @ xy.conj().T - y).max())
    print("200 random trials passed; max residual %.2e" % worst)
    # degenerate blocks: Bloch chains for angles 0, 120, 150, 180 deg
    for deg in (0, 60, 120, 150, 180):
        th = np.radians(deg)
        m = np.array([np.sin(th), 0, np.cos(th)])
        q = bloch_chain(np.array([0, 0, 1.0]), m)
        angs = [np.degrees(np.arccos(np.clip(q[i] @ q[i + 1], -1, 1))) for i in range(4)]
        assert all(min(abs(a), abs(a - 120)) < 1e-6 for a in angs), angs
    print("degenerate block angles 0/60/120/150/180 passed")


if __name__ == "__main__":
    main()
