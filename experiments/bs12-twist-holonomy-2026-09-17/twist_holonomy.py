"""Order-p twist holonomy bound for the sharp BS(1,2) test pair (A_s, D).

Conventions (D-eigenbasis e_j, j in Z/N, N odd):
  D e_j = w^j e_j,  V e_j = e_(j+1),  W e_j = e_(j * 2^-1 mod N),  w = exp(2 pi i/N)
  A_s = W exp(i s (V + V^*)),  so W D W^* = D^2 and ||A_s D A_s^* - D^2|| = O(s/N).
Fourier vectors f_m = N^-1/2 sum_j w^(-jm) e_j:  V f_m = w^m f_m, D f_m = f_(m-1),
  W f_m = f_(2m),  A_s f_m = phi(m) f_(2m),  phi(m) = exp(2 i s cos(2 pi m/N)).

Lemma (checked in part 1): if u is unitary, u^p = 1, C u C^* = u^2 and 2^L = 1 mod p,
then C^L commutes with u, and with xi = f_0, eta = f_(N/p),
  |exp(2isL) - hol_p(s)| <= 2 L ||C - A_s|| + 2 kappa,
  kappa = min_theta || u f_0 - e^(i theta) f_(N/p) ||,
  hol_p(s) = prod over the doubling orbit of N/p of phi = exp(2 i s sum_k cos(2 pi 2^k/p)).
For p = 3 (L = 2): 2|sin 3s| <= 4 eps + 2 kappa.

Part 2: for the Fourier gauge class Z = h(V) D h(V)^*, u = Z^(N/3) has kappa = 0, so every
exact C for such Z has ||C - A_s|| >= |sin 3s|/2, uniformly in N.  An LP over the monomial
subclass C = c h(V) W h(V)^* shows the constant 3/2 (as s -> 0) is attained.
"""
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(20260917)


def base(N, s):
    w = np.exp(2j * np.pi / N)
    D = np.diag(w ** np.arange(N))
    V = np.roll(np.eye(N), 1, axis=0)  # V e_j = e_(j+1)
    inv2 = pow(2, -1, N)
    W = np.zeros((N, N))
    for j in range(N):
        W[(j * inv2) % N, j] = 1
    H = V + V.T
    ev, U = np.linalg.eigh(H)
    E = (U * np.exp(1j * s * ev)) @ U.conj().T
    A = W @ E
    F = np.array([[w ** (-j * m) for m in range(N)] for j in range(N)]) / np.sqrt(N)  # columns f_m
    return D, V, W, A, F


def op(X):
    return np.linalg.norm(X, 2)


def kappa(u, F, N, p):
    x = u @ F[:, 0]
    y = F[:, (-(N // p)) % N]  # eta = D^(N/p) f_0 = f_(-N/p)
    return np.sqrt(max(0.0, 2 - 2 * abs(np.vdot(y, x))))


def orbit_hol(p, s):
    """L = ord_p(2) and the holonomy exp(2is sum cos) over the doubling orbit of -1/p."""
    L, k, tot = 0, (-1) % p, 0.0
    while True:
        tot += np.cos(2 * np.pi * k / p)
        L += 1
        k = (2 * k) % p
        if k == (-1) % p:
            break
    return L, np.exp(2j * s * tot)


def check_lemma(N=27, s=0.5, p=3, trials=60):
    """Exact pairs (C, Z) near the LP-optimal monomial pair, perturbed off the gauge class so that
    kappa > 0; u = Z^(N/p).  Verify 2 L eps + 2 kappa >= |exp(2isL) - hol_p(s)|.  Returns min slack
    and the smallest eps seen (so the test is run close to the floor, not far from it)."""
    D, V, W, A, F = base(N, s)
    L, hol = orbit_hol(p, s)
    target = abs(np.exp(2j * s * L) - hol)
    t, x = monomial_lp(N, s)
    al, a = x[:N], x[N]
    Mh = F @ np.diag(np.exp(1j * al)) @ F.conj().T
    worst, emin = np.inf, np.inf
    for tr in range(trials):
        X = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
        Hx = (X + X.conj().T) / (2 * np.sqrt(N))
        ev, U = np.linalg.eigh(Hx)
        R = (U * np.exp(1j * rng.uniform(0, 0.4) * ev)) @ U.conj().T
        G = R @ Mh
        g = np.exp(1j * (a + rng.normal(0, 0.05, N)))
        C = G @ W @ np.diag(g) @ G.conj().T
        Z = G @ D @ G.conj().T
        assert op(C @ Z @ C.conj().T - Z @ Z) < 1e-9
        u = np.linalg.matrix_power(Z, N // p)
        assert op(np.linalg.matrix_power(u, p) - np.eye(N)) < 1e-8
        assert op(C @ u @ C.conj().T - u @ u) < 1e-8
        eps = op(C - A)
        k = kappa(u, F, N, p)
        worst = min(worst, 2 * L * eps + 2 * k - target)
        emin = min(emin, eps)
    return worst, emin, target / (2 * L)


def gauge_class_kappa(N, s, trials=20):
    """Fourier gauge Z = h(V) D h(V)^*, any h: u = Z^(N/3) is an order-3 twist for EVERY exact C
    (C u C^* = (C Z C^*)^(N/3) = u^2), and kappa = 0.  Returns max kappa over random h (should be 0),
    so the lemma gives ||C - A_s|| >= |sin 3s|/2 for every exact C with such a Z."""
    D, V, W, A, F = base(N, s)
    worst = 0.0
    for t in range(trials):
        h = np.exp(1j * rng.uniform(-np.pi, np.pi, N))
        Mh = F @ np.diag(h) @ F.conj().T
        u = np.linalg.matrix_power(Mh @ D @ Mh.conj().T, N // 3)
        worst = max(worst, kappa(u, F, N, 3))
    return worst


def monomial_lp(N, s):
    """min t: |a + al(2m) - al(m) - 2s cos(2 pi m/N)| <= t, |al(m-1) - al(m)| <= t (no 2pi jumps)."""
    nv = N + 2  # al(0..N-1), a, t
    rows, rhs = [], []
    for m in range(N):
        r = np.zeros(nv)
        r[(2 * m) % N] += 1
        r[m] -= 1
        r[N] = 1
        gm = 2 * s * np.cos(2 * np.pi * m / N)
        for sg in (1, -1):
            rr = sg * r.copy()
            rr[N + 1] = -1
            rows.append(rr)
            rhs.append(sg * gm)
        r = np.zeros(nv)
        r[(m - 1) % N] += 1
        r[m] -= 1
        for sg in (1, -1):
            rr = sg * r.copy()
            rr[N + 1] = -1
            rows.append(rr)
            rhs.append(0.0)
    c = np.zeros(nv)
    c[-1] = 1
    res = linprog(c, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=[(None, None)] * nv, method="highs")
    return res.fun, res.x


def realize(N, s, x):
    """Build the exact monomial pair from an LP solution and measure both operator distances."""
    D, V, W, A, F = base(N, s)
    al, a = x[:N], x[N]
    Mh = F @ np.diag(np.exp(1j * al)) @ F.conj().T
    C = np.exp(1j * a) * Mh @ W @ Mh.conj().T
    Z = Mh @ D @ Mh.conj().T
    assert op(C @ Z @ C.conj().T - Z @ Z) < 1e-9
    return op(C - A), op(Z - D), op(A @ D @ A.conj().T - D @ D)


if __name__ == "__main__":
    print("Part 1: lemma 2L eps + 2 kappa >= |e^(2isL) - hol_p| near the floor (min slack must be >= 0)")
    for N, s, p in [(9, 0.5, 3), (27, 0.5, 3), (27, 0.2, 3), (45, 0.9, 3), (21, 0.5, 7), (63, np.pi / 3, 7)]:
        w_, e_, f_ = check_lemma(N, s, p)
        print("  N=%d s=%.3f p=%d  min slack %.4f  min eps seen %.4f  eps-floor(kappa=0) %.4f" % (N, s, p, w_, e_, f_))
    print("Part 2: Fourier gauge class Z = h(V) D h(V)^*: max kappa over random h (must be ~0)")
    for N in [27, 81, 243]:
        print("  N=%d  max kappa %.2e" % (N, gauge_class_kappa(N, 0.5)))
    print("Part 3: monomial LP optimum t (phase) and realized distances; t/s should be 1.5")
    for s in [0.02, 0.1, 0.5]:
        for N in [9, 27, 81, 243, 729]:
            t, x = monomial_lp(N, s)
            line = "  s=%.2f N=%4d  t=%.6f  t/s=%.4f  floor |sin3s|/2=%.4f" % (s, N, t, t / s, abs(np.sin(3 * s)) / 2)
            if N <= 243:
                eC, eZ, dl = realize(N, s, x)
                line += "  ||C-A||=%.4f ||Z-D||=%.4f defect=%.2e" % (eC, eZ, dl)
            print(line)
    print("Part 4: p = 7 (L = 3) bound 2|sin(7s/2)| <= 6 eps + 2 kappa; at s = pi/3 p=3 is silent")
    s = np.pi / 3
    print("  p=3 floor %.2e   p=7 floor %.4f" % (abs(np.sin(3 * s)) / 2, abs(2 * np.sin(3.5 * s)) / 6))
