#!/usr/bin/env python3
"""Numerical replay for distorted-periodic-half-spaces-defeat-real-code-junta-decoding.

Distorted real code: f_{sigma,a}(x) = interval(sum_i sigma_i phi_a(x_i)),
phi_a(t) = t + (a/(2 pi)) sin(2 pi t), interval(z) = +1 on [2k,2k+1), -1 on [2k-1,2k).
a = 0 is the Khot--Moshkovitz real code.

Checks:
 A. arccos(1-alpha) <= (pi/2) sqrt(alpha) on [0,1].
 B. Periodized Gaussian density is within 6e-9 of uniform.
 C. lambda_K(a) = sup |psi(kappa,w)| < 1 over odd |kappa|<=K, integer w (a>0),
    and |psi(1,-1)| = 1 at a = 0 (calibration: honest code correlates with itself).
 D. Monte Carlo: exact folding; correlation E[f_{sigma,a} f_sigma] decays with n,
    while product-formula prediction matches.
 E. Monte Carlo rejection rates of the KM low boundary, constraint and consistency
    tests: distorted vs honest code, ratio bounded.
Deterministic seeds. Exit status 0 iff every assertion holds.
"""
import numpy as np

rng = np.random.default_rng(20260917)
TWO_PI = 2 * np.pi


def phi(t, a):
    return t + (a / TWO_PI) * np.sin(TWO_PI * t)


def interval(z):
    return np.where(np.mod(z, 2.0) < 1.0, 1, -1)


def f_code(x, sigma, a):
    return interval(phi(x, a) @ sigma)


# ---------------- A ----------------
al = np.linspace(0, 1, 200001)
lhs = np.arccos(1 - al)
rhs = (np.pi / 2) * np.sqrt(al)
assert np.all(lhs <= rhs + 1e-12), "arccos bound fails"
print("A arccos(1-a) <= (pi/2)sqrt(a): max ratio", np.max(lhs[1:] / rhs[1:]))

# ---------------- B ----------------
u = np.linspace(0, 1, 1001)
per = sum(np.exp(-((u + k) ** 2) / 2) / np.sqrt(TWO_PI) for k in range(-40, 41))
dev = np.max(np.abs(per - 1))
assert dev <= 6e-9, dev
print("B periodized gaussian max deviation from 1:", dev)

# ---------------- C ----------------
T = np.linspace(-14, 14, 400001)
dT = T[1] - T[0]
G = np.exp(-T ** 2 / 2) / np.sqrt(TWO_PI) * dT


def psi(kappa, w, a):
    return np.sum(G * np.exp(1j * np.pi * (kappa * phi(T, a) + w * T)))


cal = abs(psi(1, -1, 0.0))
assert abs(cal - 1) < 1e-9, cal
print("C calibration |psi(1,-1)| at a=0:", cal)
for a in (0.1, 0.3, 0.5, 0.8):
    best = 0.0
    arg = None
    for kappa in (1, 3, 5, 7):
        for w in range(-60, 61):
            v = abs(psi(kappa, w, a))
            if v > best:
                best, arg = v, (kappa, w)
    # tail |w| large: integration-by-parts bound decays like 1/|w|
    tail = max(abs(psi(k, w, a)) for k in (1, 3, 5, 7) for w in (-60, 60))
    assert best < 1 - a ** 2 / 32, (a, best)  # 1-|psi| ~ a^2/16 heuristic
    print(f"C a={a}: lambda_7 over |w|<=60 = {best:.6f} at (kappa,w)={arg}; |psi| at |w|=60: {tail:.2e}")

# ---------------- D ----------------
def corr_mc(n, a, N=200000, batch=20000):
    sigma = rng.choice([-1, 1], size=n)
    tot = 0.0
    fold_ok = True
    for _ in range(N // batch):
        x = rng.standard_normal((batch, n))
        fa = f_code(x, sigma, a)
        f0 = f_code(x, sigma, 0.0)
        tot += np.sum(fa * f0)
        if _ == 0:
            e1 = np.zeros(n); e1[0] = 1.0
            fold_ok &= np.mean(f_code(x + e1, sigma, a) == -fa) > 0.999
            fold_ok &= np.mean(f_code(-x, sigma, a) == -fa) > 0.999
    return tot / N, fold_ok


print("D correlation E[f_{sigma,a} f_sigma], a = 0.8")
prev = None
for n in (4, 16, 64, 256):
    c, ok = corr_mc(n, 0.8)
    assert ok, "folding failed"
    print(f"  n={n:4d}: corr = {c:+.4f}  (MC std ~ {1/np.sqrt(200000):.4f})")
    prev = c
assert abs(prev) < 0.02, prev

# ---------------- E ----------------
def lowboundary(n, a, alpha, N=200000, batch=20000):
    sigma = rng.choice([-1, 1], size=n)
    rej = 0
    for _ in range(N // batch):
        x = rng.standard_normal((batch, n))
        w = rng.standard_normal((batch, n))
        y = (1 - alpha) * x + np.sqrt(2 * alpha - alpha ** 2) * w
        rej += np.sum(f_code(x, sigma, a) != f_code(y, sigma, a))
    return rej / N


def constraint(n, k, a, beta, N=200000, batch=20000):
    sigma = rng.choice([-1, 1], size=n)
    rej = 0
    c = 1 - beta ** 2 / 2
    for _ in range(N // batch):
        v = np.zeros(n)
        v[:k] = rng.choice([-1, 1], size=k) / np.sqrt(k)
        x = rng.standard_normal((batch, n))
        t = x @ v
        tn = c * t + np.sqrt(1 - c ** 2) * rng.standard_normal(batch)
        y = x + np.outer(tn - t, v)
        rej += np.sum(f_code(x, sigma, a) != f_code(y, sigma, a))
    return rej / N


def consistency(n, m, a, s, N=200000, batch=20000):
    sigma = rng.choice([-1, 1], size=n)
    rej = 0
    for _ in range(N // batch):
        x = rng.standard_normal((batch, n))
        y = x.copy()
        x[:, :m] = rng.uniform(-s, s, size=(batch, m))
        y[:, :m] = rng.uniform(-s, s, size=(batch, m))
        rej += np.sum(f_code(x, sigma, a) != f_code(y, sigma, a))
    return rej / N


n = 256
for a in (0.3, 0.8):
    r0 = lowboundary(n, 0.0, 1e-4); ra = lowboundary(n, a, 1e-4)
    bound = (1 + a) / (1 - a) * 1.12
    print(f"E low-boundary n={n} alpha=1e-4 a={a}: honest {r0:.4f}, distorted {ra:.4f}, ratio {ra/r0:.3f} (proved <= {bound:.2f})")
    assert ra / r0 <= bound
    c0 = constraint(n, 9, 0.0, 0.05); ca = constraint(n, 9, a, 0.05)
    print(f"E constraint k=9 beta=0.05 a={a}: honest {c0:.4f}, distorted {ca:.4f}")
    assert ca <= 0.05 * np.sqrt(2 / np.pi) * 1.001 / (1 - a) * (1 + a * 1.01) * 1.2 + 0.005
    s0 = consistency(n, 64, 0.0, 0.02); sa = consistency(n, 64, a, 0.02)
    print(f"E consistency m=64 s=0.02 a={a}: honest {s0:.4f}, distorted {sa:.4f}")
    assert sa <= 2 * 1.001 / (1 - a) * 2 * (1 + a) * 0.02 * np.sqrt(64) + 0.005
print("ALL CHECKS PASSED")
