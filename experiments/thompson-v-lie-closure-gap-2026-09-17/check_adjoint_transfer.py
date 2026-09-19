"""Sanity checks for thompson-v-gap-witnesses-need-unbounded-lie-closure (not load-bearing).

G0 = S4 *_<a> S3, V = G0/<<r5..r8>>, D(rho) = max_i ||rho(r_i) - 1||_op (words in
../thompson-v-models/rel_V.txt).  Checks, on random exact representations sigma of G0:

 (T1) adjoint transfer: D(sigma (x) conj(sigma)) <= 2 D(sigma).  sigma (x) conj(sigma) is the
      complexified conjugation action on M_n = u(n)_C, which contains the complexified adjoint
      action on Lie(closure); the route proves ||Ad(u) - 1|| <= 2 ||u - 1|| on Hilbert--Schmidt space.
 (T2) Sym^m tower of a 2-dim sigma: every nontrivial Sym^m sigma has closure whose derived algebra
      is (a quotient of) su(2), so the route predicts
          D(Sym^m sigma) >= min(1/2, D(Ad_su2 sigma)/2)   for every m,
      where Ad_su2 sigma is the 3-dim adjoint action on traceless skew-Hermitian matrices.
      (For 2-dim sigma, D(Ad_su2 sigma) >= delta_3 > 0 whenever Ad_su2 sigma is nontrivial.)
      Sym^m(w) is normal with eigenvalues e^{i((m-j)x + j y)} when w has eigenvalues e^{ix}, e^{iy},
      so D(Sym^m sigma) is computed exactly from the spectra of the sigma(r_i).

Usage: python3 check_adjoint_transfer.py > out_check_adjoint_transfer.txt
"""
import os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MODELS = os.path.join(HERE, "..", "thompson-v-models")
sys.path.insert(0, MODELS)
import texwords  # noqa: E402

rng = np.random.default_rng(20260919)
WORDS = [texwords.parse(l.strip()) for l in open(os.path.join(MODELS, "rel_V.txt")) if l.strip()]


def perm_matrix(p):
    n = len(p)
    M = np.zeros((n, n))
    for i, j in enumerate(p):
        M[j, i] = 1.0
    return M


def restrict(Ms, basis):
    return [basis.T @ M @ basis for M in Ms]


def orth_complement_of_ones(n):
    Q, _ = np.linalg.qr(np.column_stack([np.ones(n)] + [np.eye(n)[:, i] for i in range(n - 1)]))
    return Q[:, 1:]


def diag_a(gens):
    w, U = np.linalg.eigh(gens[0])
    U = U[:, np.argsort(-w)]
    return [U.T @ g @ U for g in gens]


def s4_two():
    pairings = [frozenset([frozenset([0, 1]), frozenset([2, 3])]), frozenset([frozenset([0, 2]), frozenset([1, 3])]),
                frozenset([frozenset([0, 3]), frozenset([1, 2])])]

    def on_pairings(p):
        return tuple(pairings.index(frozenset(frozenset(p[x] for x in blk) for blk in pr)) for pr in pairings)

    a3, b3 = perm_matrix(on_pairings((1, 0, 2, 3))), perm_matrix(on_pairings((0, 2, 3, 1)))
    return diag_a(restrict([a3, b3], orth_complement_of_ones(3)))


def s4_three():
    a, b = perm_matrix((1, 0, 2, 3)), perm_matrix((0, 2, 3, 1))
    return diag_a(restrict([a, b], orth_complement_of_ones(4)))


def s3_two():
    a, c = perm_matrix((1, 0, 2)), perm_matrix((0, 2, 1))
    return diag_a(restrict([a, c], orth_complement_of_ones(3)))


def haar(n):
    Z = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / np.abs(np.diag(R)))


def rep(n):
    """Random exact representation (A, B, C) of G0 with a = diag(1_(n-1), -1)."""
    if n == 2:
        (A, B), (_, C3) = s4_two(), s3_two()
        W = np.diag(np.exp(1j * rng.uniform(0, 2 * np.pi, 2)))
    else:  # n == 3: S4 standard (a = diag(1,1,-1)) against S3 trivial (+) two-dim (a = diag(1,1,-1))
        (A, B), (_, c3) = s4_three(), s3_two()
        C3 = np.zeros((3, 3))
        C3[0, 0] = 1.0
        C3[1:, 1:] = c3
        W = np.zeros((3, 3), complex)
        W[:2, :2] = haar(2)
        W[2, 2] = np.exp(1j * rng.uniform(0, 2 * np.pi))
    return A.astype(complex), B.astype(complex), W @ C3 @ W.conj().T


def word(wd, A, B, C):
    M = np.eye(A.shape[0], dtype=complex)
    Bi = B.conj().T
    for l, e in wd:
        M = M @ ({"a": A, "c": C}[l] if l in "ac" else (B if e > 0 else Bi))
    return M


def opn(X):
    return np.linalg.norm(X, 2)


def main():
    for n in (2, 3):  # the relations of G0 hold exactly
        A, B, C = rep(n)
        I = np.eye(n)
        assert np.allclose(A @ A, I) and np.allclose(np.linalg.matrix_power(B, 3), I)
        assert np.allclose(np.linalg.matrix_power(A @ B, 4), I) and np.allclose(C @ C, I)
        assert np.allclose(np.linalg.matrix_power(A @ C, 3), I)
    worst_T1, worst_T2, n_T1, n_T2 = -1e9, -1e9, 0, 0
    minD, minAd = {2: 9.0, 3: 9.0}, 9.0
    for trial in range(4000):
        n = 2 if trial % 2 == 0 else 3
        A, B, C = rep(n)
        R = [word(w, A, B, C) for w in WORDS]
        D = max(opn(X - np.eye(n)) for X in R)
        minD[n] = min(minD[n], D)
        Dad = max(opn(np.kron(X, X.conj()) - np.eye(n * n)) for X in R)
        worst_T1 = max(worst_T1, Dad - 2 * D)
        n_T1 += 1
        if n == 2:
            specs = [np.angle(np.linalg.eigvals(X)) for X in R]
            Dsu2 = max(abs(np.exp(1j * (s[0] - s[1])) - 1) for s in specs)
            minAd = min(minAd, Dsu2)
            for m in range(1, 41):
                Dm = max(max(abs(np.exp(1j * ((m - j) * s[0] + j * s[1])) - 1) for j in range(m + 1)) for s in specs)
                worst_T2 = max(worst_T2, min(0.5, Dsu2 / 2) - Dm)
                n_T2 += 1
    print(f"T1 checks {n_T1}: max of D(sigma x conj sigma) - 2 D(sigma) = {worst_T1:.3e} (must be <= 0)")
    print(f"T2 checks {n_T2} (m = 1..40): max of min(1/2, D_ad/2) - D(Sym^m) = {worst_T2:.3e} (must be <= 0)")
    print(f"min D over sampled 2-dim reps = {minD[2]:.4f}; 3-dim = {minD[3]:.4f}; "
          f"min D(Ad_su2) over sampled 2-dim = {minAd:.4f}")
    assert worst_T1 <= 1e-9 and worst_T2 <= 1e-9
    print("OK")


if __name__ == "__main__":
    main()
