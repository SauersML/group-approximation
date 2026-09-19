"""Order-type kernels of T-bar on the dyadic line are bounded: numerical calibration.

A T-bar-invariant kernel on the dyadic orbit Z[1/2] of 0 has the form
    k(x, y) = a_n  if |x - y| in (n, n+1),   b_n if |x - y| = n >= 1,   0 if x = y.
The theorem in research/lifted-thompson-t-order-type-kernels-bounded-on-centre.md says
k is conditionally negative definite (cnd) only if all a_n are equal.  Here we test
generic configurations (no integer differences, so only the a_n matter) and report
lambda = max eigenvalue of P K P, with P the projection onto sum-zero vectors.
k is cnd on the configuration iff lambda <= 0 (up to rounding).

Run: python3 check.py
"""
import numpy as np

rng = np.random.default_rng(20260917)


def lam(a, N, M):
    """N points per unit length on [0, M), generic offsets; a(n) gives a_n."""
    pts = np.arange(N * M) / N + rng.uniform(0, 1.0 / (4 * N), N * M)
    d = np.abs(pts[:, None] - pts[None, :])
    K = np.vectorize(a)(np.floor(d).astype(int)).astype(float)
    np.fill_diagonal(K, 0.0)
    n = len(pts)
    P = np.eye(n) - np.ones((n, n)) / n
    return np.linalg.eigvalsh(P @ K @ P).max()


tests = {
    "constant a_n = 1 (should pass)": lambda n: 1.0,
    "a_n = n + 1 (ceil metric)": lambda n: n + 1.0,
    "a_n = log(n + 2)": lambda n: np.log(n + 2.0),
    "a_n = sqrt(n + 1)": lambda n: np.sqrt(n + 1.0),
    "single jump a_0 = 1, a_n = 1.05 (n >= 1)": lambda n: 1.0 if n == 0 else 1.05,
    "single dip a_0 = 1, a_n = 0.95 (n >= 1)": lambda n: 1.0 if n == 0 else 0.95,
}

if __name__ == "__main__":
    for name, a in tests.items():
        row = []
        for N in (2, 4, 8, 16, 32, 64):
            row.append(lam(a, N, 6))
        print(f"{name:45s} " + " ".join(f"{v:9.4f}" for v in row))
    print("columns: N = 2, 4, 8, 16, 32, 64 points per unit, window [0, 6)")
    print("prediction: every nonconstant row becomes positive once N is large;")
    print("for a single jump of size eps at distance 1 the threshold is N ~ 1/(0.43 eps),")
    print("0.43 = -min of the Fourier transform 2 sin(x)/x of the indicator of (-1, 1)")
