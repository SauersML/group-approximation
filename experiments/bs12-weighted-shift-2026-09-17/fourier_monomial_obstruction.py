"""Fourier-monomial corrections of the Bessel-twisted BS(1,2) pair.

Setting (e-basis of C^N, N odd): D e_j = w^j e_j, V e_j = e_(j+1),
W e_j = e_(j/2), A_s = W exp(i s (V+V^*)).  Fourier basis
f_m = N^(-1/2) sum_j w^(-jm) e_j, so V f_m = w^m f_m, D f_m = f_(m-1),
W f_m = f_(2m) and A_s f_m = exp(i g_m) f_(2m), g_m = 2 s cos(2 pi m/N).

Class F: pairs C f_m = e^(i a_m) f_(2m), Z f_m = e^(i t_m) f_(m-1).
Exact iff t_(2m) + t_(2m-1) - t_m = a_(m-1) - a_m (mod 2 pi) for all m.

Checks:
 1. y_m = r(m)/N - (N+1)/(2N), r(m) in {1..N} the representative of m,
    satisfies y_(2m) = y_m + y_(m+h), h=(N+1)/2  (exact rationals).
 2. matrix identities of the setting (numerically, N=27).
 3. random exact pairs in class F satisfy a_0 = mean(a).
 4. LP: the exact class-F distance in angle sup-norm,
      t* = min max(|b|_inf, |t|_inf)  s.t.  T t = grad(g+b),
    compared with the proved lower bound s.
Run: python3 fourier_monomial_obstruction.py
"""
from fractions import Fraction as F
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog


def check_bernoulli(N):
    h = (N + 1) // 2
    rep = lambda m: m if m else N
    y = [F(2 * rep(m) - N - 1, 2 * N) for m in range(N)]
    return all(y[(2 * m) % N] == y[m] + y[(m + h) % N] for m in range(N))


def matrices(N, s):
    w = np.exp(2j * np.pi / N)
    j = np.arange(N)
    D = np.diag(w ** j)
    V = np.roll(np.eye(N), 1, axis=0)          # V e_j = e_(j+1)
    h = (N + 1) // 2
    W = np.zeros((N, N)); W[(j * h) % N, j] = 1  # W e_j = e_(j/2)
    H = V + V.T
    ev, U = np.linalg.eigh(H)
    A = W @ (U @ np.diag(np.exp(1j * s * ev)) @ U.T)
    Fm = np.array([w ** (-j * m) for m in range(N)]).T / np.sqrt(N)  # cols f_m
    return D, V, W, A, Fm


def check_setting(N=27, s=0.3):
    D, V, W, A, Fm = matrices(N, s)
    m = np.arange(N)
    g = 2 * s * np.cos(2 * np.pi * m / N)
    err = 0.0
    for k in range(N):
        f = Fm[:, k]
        err = max(err, np.abs(D @ f - Fm[:, (k - 1) % N]).max(),
                  np.abs(A @ f - np.exp(1j * g[k]) * Fm[:, (2 * k) % N]).max())
    defect = np.linalg.norm(A @ D @ A.conj().T - D @ D, 2)
    return err, defect


def T_matrix(N):
    r, c, v = [], [], []
    for k in range(N):
        for col, val in (((2 * k) % N, 1.0), ((2 * k - 1) % N, 1.0), (k, -1.0)):
            r.append(k); c.append(col); v.append(val)
    return sp.csr_matrix((v, (r, c)), shape=(N, N))


def grad_matrix(N):  # (grad a)_m = a_(m-1) - a_m
    r = list(range(N)) * 2
    c = [(m - 1) % N for m in range(N)] + list(range(N))
    v = [1.0] * N + [-1.0] * N
    return sp.csr_matrix((v, (r, c)), shape=(N, N))


def random_exact_pairs(N, trials, rng):
    T, G = T_matrix(N).toarray(), grad_matrix(N).toarray()
    worst_rel, worst_mean = 0.0, 0.0
    for _ in range(trials):
        t = rng.normal(size=N) * 0.1
        t -= t.mean()                        # sum t = 0 is needed
        rhs = T @ t
        a = np.linalg.lstsq(G, rhs, rcond=None)[0]
        worst_rel = max(worst_rel, np.abs(G @ a - rhs).max())
        worst_mean = max(worst_mean, abs(a[0] - a.mean()))
    return worst_rel, worst_mean


def cycles(N):
    seen, out = set(), []
    for m in range(N):
        if m in seen:
            continue
        c, x = [], m
        while x not in seen:
            seen.add(x); c.append(x); x = (2 * x) % N
        out.append(c)
    return out


def cycle_check(N, trials, rng):
    T, G = T_matrix(N).toarray(), grad_matrix(N).toarray()
    worst = 0.0
    for _ in range(trials):
        t = rng.normal(size=N) * 0.1
        t -= t.mean()
        a = np.linalg.lstsq(G, T @ t, rcond=None)[0]
        worst = max(worst, max(abs(a[c].mean() - a.mean()) for c in cycles(N)))
    return worst


def lp_distance(N, s):
    m = np.arange(N)
    g = 2 * s * np.cos(2 * np.pi * m / N)
    T, G = T_matrix(N), grad_matrix(N)
    # variables x = [b (N), t (N), tau]; minimize tau
    Aeq = sp.hstack([-G, T, sp.csr_matrix((N, 1))])
    beq = G @ g
    I = sp.identity(N)
    z = sp.csr_matrix((N, N)); one = sp.csr_matrix(np.ones((N, 1)))
    Aub = sp.vstack([sp.hstack([I, z, -one]), sp.hstack([-I, z, -one]),
                     sp.hstack([z, I, -one]), sp.hstack([z, -I, -one])])
    cost = np.zeros(2 * N + 1); cost[-1] = 1
    res = linprog(cost, A_ub=Aub, b_ub=np.zeros(4 * N), A_eq=Aeq, b_eq=beq,
                  bounds=[(None, None)] * (2 * N) + [(0, None)], method="highs")
    return res.x[-1] if res.success else float("nan")


if __name__ == "__main__":
    odd = [n for n in range(3, 400, 2)]
    print("1. Bernoulli cokernel identity holds for all odd N < 400:",
          all(check_bernoulli(n) for n in odd))
    err, defect = check_setting()
    print(f"2. setting identities, N=27 s=0.3: max err {err:.2e}, "
          f"relator defect {defect:.4f} (bound 4 pi s/N = {4*np.pi*0.3/27:.4f})")
    rel, mean = random_exact_pairs(45, 50, np.random.default_rng(1))
    print(f"3. random exact class-F pairs, N=45: residual {rel:.1e}, "
          f"max |a_0 - mean a| {mean:.1e}")
    for N in (25, 27, 35, 45, 63):
        print(f"3b. N={N}: max over cycles |avg_cycle a - mean a| = "
              f"{cycle_check(N, 20, np.random.default_rng(N)):.1e}")
    print("4. LP class-F angle distance t*/s (lower bound proved: 1; 1.5 if 3|N)")
    for s in (0.05, 0.1, 0.3):
        row = [f"N={N}: {lp_distance(N, s)/s:.4f}"
               for N in (27, 81, 243, 729, 25, 35, 125)]
        print(f"   s={s}: " + ", ".join(row))
