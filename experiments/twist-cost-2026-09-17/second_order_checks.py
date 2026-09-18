"""Numerical sanity checks for lifted-thompson-t-root-twist-cost-iff-euler-cup-product.

These checks do not prove anything about Thompson's group. They test the two exact
identities used in the proof, and show that the square-root lower bound is attained
in order by the Heisenberg (clock and shift) relation, which has the same algebraic
shape as the Euler extension of a surface group.

Check 1 (primitive of the Kahler cocycle).
  For unitaries A = pi(g), B = pi(h), AB = pi(gh), and a unit vector xi, put
  b(x) = pi(x) xi - xi and u(x) = 1 - <pi(x) xi, xi>.  Then
      Im u(g) + Im u(h) - Im u(gh) = Im <b(g), pi(g) b(h)>
  with the inner product conjugate-linear in the first slot.

Check 2 (second-order expansion of a word with zero exponent sums).
  For a word w of length m with zero exponent sum in every letter,
      |<pi(w) xi, xi> - 1| <= (m^2 / 2) * max_s ||pi(s) xi - xi||^2 .

Check 3 (clock and shift).  X, Z of size n with Z X = e(1/n) X Z.  The commutator
  word w = X Z X^-1 Z^-1 (m = 4) is the scalar e(-1/n).  The minimal value of
  max(||X xi - xi||, ||Z xi - xi||) over unit xi is compared with the lower bound
  sqrt(2 |e(1/n) - 1|) / m.  Both scale like n^(-1/2).
"""

import numpy as np

rng = np.random.default_rng(20260917)


def inner(x, y):
    # conjugate-linear in the first argument
    return np.vdot(x, y)


def random_unitary(d):
    q, r = np.linalg.qr(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)))
    return q * (np.diag(r) / np.abs(np.diag(r)))


def check1(trials=200, d=6):
    worst = 0.0
    for _ in range(trials):
        A, B = random_unitary(d), random_unitary(d)
        xi = rng.normal(size=d) + 1j * rng.normal(size=d)
        xi /= np.linalg.norm(xi)
        b = lambda U: U @ xi - xi
        u = lambda U: 1 - inner(U @ xi, xi)
        lhs = (u(A) + u(B) - u(A @ B)).imag
        rhs = inner(b(A), A @ b(B)).imag
        worst = max(worst, abs(lhs - rhs))
    return worst


def check2(trials=200, d=6, eps=0.05):
    # near-identity unitaries exp(i eps H), word = commutator of products
    worst_ratio = 0.0
    for _ in range(trials):
        mats = []
        for _k in range(3):
            H = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
            H = (H + H.conj().T) / 2
            w, V = np.linalg.eigh(H)
            mats.append(V @ np.diag(np.exp(1j * eps * w)) @ V.conj().T)
        a, b_, c = mats
        inv = lambda U: U.conj().T
        # w = [a b, c] a^-1 ... use: a b c a^-1 b^-1 c^-1 (zero exponent sums, m = 6)
        W = a @ b_ @ c @ inv(a) @ inv(b_) @ inv(c)
        m = 6
        xi = rng.normal(size=d) + 1j * rng.normal(size=d)
        xi /= np.linalg.norm(xi)
        delta = max(np.linalg.norm(U @ xi - xi) for U in mats)
        lhs = abs(inner(W @ xi, xi) - 1)
        worst_ratio = max(worst_ratio, lhs / (m * m / 2 * delta ** 2))
    return worst_ratio


def clock_shift(n):
    Z = np.diag(np.exp(2j * np.pi * np.arange(n) / n))
    X = np.roll(np.eye(n), 1, axis=0)
    return X, Z


def check3(ns=(8, 16, 32, 64, 128, 256)):
    rows = []
    for n in ns:
        X, Z = clock_shift(n)
        C = X @ Z @ X.conj().T @ Z.conj().T
        scalar = C[0, 0]
        assert np.allclose(C, scalar * np.eye(n))
        # sum of squared defects is <xi, H xi> with H = sum (2 - U - U^*)
        H = sum(2 * np.eye(n) - U - U.conj().T for U in (X, Z))
        w, V = np.linalg.eigh(H)
        xi = V[:, 0]
        dmax = max(np.linalg.norm(U @ xi - xi) for U in (X, Z))
        lower = np.sqrt(2 * abs(scalar - 1)) / 4
        rows.append((n, dmax, lower, dmax * np.sqrt(n), lower * np.sqrt(n)))
    return rows


if __name__ == "__main__":
    print("check1 max |d Im u - omega| =", check1())
    print("check2 max ratio |<w xi,xi>-1| / (m^2/2 delta^2) =", check2())
    print("check3  n   max-defect(ground state)  lower bound  both times sqrt(n)")
    for n, d, lo, ds, ls in check3():
        print(f"      {n:4d}   {d:.5f}               {lo:.5f}     {ds:.4f}  {ls:.4f}")
