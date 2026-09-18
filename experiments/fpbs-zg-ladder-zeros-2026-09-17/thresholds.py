"""p_c and the l2 point of T_3 box K_2 from the R=infinity transfer matrix.

Interior rung r(p)=1-(1-p)(1-p^2 g*), g* the limit of g_R (monotone in R).
tau(o,(v_k,i)) ~ c mu(p)^k with mu = Perron root of T(r).  Depth-k sphere
has 3*2^(k-1) tree vertices, so E|C(o)| < inf iff 2 mu < 1 (p_c=p_T), and
sum_x tau^2 < inf iff 2 mu^2 < 1 (the l2 point p_2 of tau_p).
"""
import numpy as np


def gstar(p, iters=4000):
    g = 0.0
    for _ in range(iters):
        g = 1 - (1 - p) * (1 - p * p * g) ** 2
    return g


def mu(p):
    r = 1 - (1 - p) * (1 - p * p * gstar(p))
    a = p * (1 - p)
    T = np.array([[p * p + 2 * a * r, a * (1 - r), a * (1 - r)],
                  [p * r, p * (1 - r), 0.0],
                  [p * r, 0.0, p * (1 - r)]])
    return max(abs(np.linalg.eigvals(T)))


def solve(target):
    lo, hi = 1e-6, 1 - 1e-6
    for _ in range(80):
        m = (lo + hi) / 2
        if mu(m) < target:
            lo = m
        else:
            hi = m
    return (lo + hi) / 2


if __name__ == "__main__":
    pc = solve(0.5)
    p2 = solve(2 ** -0.5)
    rho = (2 * np.sqrt(2) + 1) / 4
    print(f"p_c = {pc:.10f}  (mu=1/2)")
    print(f"p_2 = {p2:.10f}  (mu=1/sqrt2, l2 point of tau)")
    print(f"rho = {rho:.10f}")
    for p in (0.3, pc, 0.45, p2, 0.7):
        print(f"  p={p:.4f} mu={mu(p):.6f} g*={gstar(p):.6f}")
