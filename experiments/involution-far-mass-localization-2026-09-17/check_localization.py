"""Numerical sanity checks for
research/invariant-norm-ratio-witnesses-localize-hyperlinear.md

Checks, with numpy:
  (1) far-mass subadditivity  F_{d1+d2}(XY) <= F_{d1}(X) + F_{d2}(Y)  on random unitaries
      with mixed atomic / spread spectra (Corollary 2 of the proof);
  (2) the localization pipeline of Steps 4-6 on a ratio-witness family for
      A_5 = <x, y | x^2, y^3, (xy)^5>, sigma = x, built as
      (exact 5-dim permutation rep (+) identity) times small spread rotations.
      The spread noise makes the family a Schatten-p ratio witness that is far from
      a metric model in normalized HS on the full space; after localization to the
      far spectral subspace E the relators are small in normalized HS on E and sigma
      is separated, as the proof predicts.
This is a check of the algebra, not part of the proof.
"""
import numpy as np

rng = np.random.default_rng(20260917)


def haar(d):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def eig(x):
    return np.linalg.eigvals(x)


def far(x, delta):
    """F_delta(x) = fraction of eigenvalues z with |z - 1| > delta."""
    z = eig(x)
    return np.mean(np.abs(z - 1) > delta)


def unitary_with_spectrum(angles):
    u = haar(len(angles))
    return u @ np.diag(np.exp(1j * np.asarray(angles))) @ u.conj().T


def expm_herm(h):
    w, v = np.linalg.eigh(h)
    return v @ np.diag(np.exp(1j * w)) @ v.conj().T


# ---------------------------------------------------------------- (1)
worst = -1.0
for trial in range(300):
    d = int(rng.integers(8, 40))
    def rand_angles():
        a = rng.normal(0, rng.uniform(0.01, 0.3), d)
        k = int(rng.integers(0, d // 3 + 1))
        a[:k] = rng.uniform(-np.pi, np.pi, k)
        return a
    x = unitary_with_spectrum(rand_angles())
    y = unitary_with_spectrum(rand_angles())
    d1, d2 = rng.uniform(0.01, 1.0, 2)
    lhs = far(x @ y, d1 + d2)
    rhs = far(x, d1) + far(y, d2)
    worst = max(worst, lhs - rhs)
print(f"(1) subadditivity: max over 300 trials of F(XY)-F(X)-F(Y) = {worst:.4f}  (must be <= 0)")
assert worst <= 1e-12

# ---------------------------------------------------------------- (2)
# A_5 on 5 points: x = (1 2)(3 4), y = (1 3 5); then (xy) has order 5.
def perm_matrix(p):
    m = np.zeros((5, 5))
    for i, j in enumerate(p):
        m[j, i] = 1
    return m

X5 = perm_matrix([1, 0, 3, 2, 4])
Y5 = perm_matrix([2, 1, 4, 3, 0])
assert np.allclose(np.linalg.matrix_power(X5, 2), np.eye(5))
assert np.allclose(np.linalg.matrix_power(Y5, 3), np.eye(5))
assert np.allclose(np.linalg.matrix_power(X5 @ Y5, 5), np.eye(5))

def words(Ux, Uy):
    inv = np.linalg.inv
    return {
        "x^2": Ux @ Ux,
        "y^3": Uy @ Uy @ Uy,
        "(xy)^5": np.linalg.matrix_power(Ux @ Uy, 5),
    }

def lp(x, p):
    z = eig(x)
    return np.mean(np.abs(z - 1) ** p) ** (1 / p)

def l2(x):
    return lp(x, 2)

p = 1.0
for d, eps in [(120, 1e-3), (200, 5e-5)]:
    base_x = np.eye(d, dtype=complex); base_x[:5, :5] = X5
    base_y = np.eye(d, dtype=complex); base_y[:5, :5] = Y5
    conj = haar(d)
    base_x = conj @ base_x @ conj.conj().T
    base_y = conj @ base_y @ conj.conj().T
    def noise():
        h = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
        h = (h + h.conj().T) / 2
        return expm_herm(eps * h / np.linalg.norm(h, 2))
    Ux = base_x @ noise()
    Uy = base_y @ noise()
    rel = words(Ux, Uy)
    sig = Ux
    ratio = max(lp(r, p) for r in rel.values()) / lp(sig, p)
    eta = np.mean(np.real(eig(sig)) < 0)
    # localization at threshold delta
    delta = 0.3
    E_cols = []
    Bs = []
    for U in (Ux, Uy):
        w, v = np.linalg.eig(U)
        # U is normal; orthonormalize eigenvectors per eigenvalue cluster via Schur
        from scipy.linalg import schur
        T, Z = schur(U, output="complex")
        w = np.diag(T)
        mask = np.abs(w - 1) > delta
        P = Z[:, mask] @ Z[:, mask].conj().T
        E_cols.append(Z[:, mask])
        Bs.append((U @ P + (np.eye(d) - P)))
    E = np.linalg.qr(np.hstack(E_cols))[0]
    D = E.shape[1]
    hat = [E.conj().T @ B @ E for B in Bs]
    # check B fixes E-perp and hat is unitary
    for B, H in zip(Bs, hat):
        assert np.allclose(H.conj().T @ H, np.eye(D), atol=1e-8)
    relE = words(hat[0], hat[1])
    print(f"(2) d={d} eps={eps}: S_1 ratio max_r L_1(r)/L_1(sigma) = {ratio:.3f}; eta = {eta:.4f}; "
          f"full-space L_2(sigma)^2 = {l2(sig)**2:.4f}")
    print(f"    localized dim D = {D}; on E: max_r L_2(r)^2 = {max(l2(r)**2 for r in relE.values()):.2e}, "
          f"L_2(sigma)^2 = {l2(hat[0])**2:.3f}")
