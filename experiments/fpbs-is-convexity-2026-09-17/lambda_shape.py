"""Exact walk rate lambda(p) on G = T_3 box K_2 and a shape test of log lambda.

Infinite-volume version of experiments/fpbs-zg-ladder-zeros-2026-09-17/
ladder_connectivity.py.  Side gadgets converge to the least fixed point h* of
h = p^2 (1 - (1-p)(1-h)^2) (iteration from h(R)=0).  Along the geodesic,
tau((v_k,i)) = c_i(p) mu(p)^k (1+o(1)), where mu(p) is the Perron root of the
3-state ladder transfer with rung r = 1-(1-p)(1-h*).  The tree distance of
SRW on G is the reflected chain with steps +1 (1/2), -1 (1/4), 0 (1/4), so
  lambda(p) = rho                          if mu(p) <= 1/sqrt 2,
  lambda(p) = 1/4 + mu/2 + 1/(4 mu)        otherwise,
with rho = 1/4 + 1/sqrt 2.  Check: finite-n values a_n^(1/n) from the exact
polynomials, and p_2 (where mu = 1/sqrt 2) against the recorded 0.52620.
"""
import sys
import numpy as np

sys.path.insert(0, "experiments/fpbs-zg-ladder-zeros-2026-09-17")


def hstar(p, iters=20000):
    h = 0.0
    for _ in range(iters):
        h2 = p * p * (1 - (1 - p) * (1 - h) ** 2)
        if abs(h2 - h) < 1e-16:
            break
        h = h2
    return h


def mu(p):
    h = hstar(p)
    r = 1 - (1 - p) * (1 - h)
    a = p * (1 - p)
    M = np.array([[p * p + 2 * a * r, p * r, p * r],
                  [a * (1 - r), p * (1 - r), 0.0],
                  [a * (1 - r), 0.0, p * (1 - r)]])
    return max(abs(np.linalg.eigvals(M)))


RHO = 0.25 + 1 / np.sqrt(2)


def lam(p):
    m = mu(p)
    return RHO if m <= 1 / np.sqrt(2) else 0.25 + m / 2 + 1 / (4 * m)


def main():
    # p_2 by bisection on mu = 1/sqrt 2
    lo, hi = 0.3, 0.9
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if mu(mid) < 1 / np.sqrt(2) else (lo, mid)
    print("p_2 (mu=1/sqrt2) =", round(lo, 6))
    # finite-n cross-check
    from ladder_connectivity import a_nR
    for p in (0.6, 0.75, 0.9):
        z = np.array([p], dtype=complex)
        a1 = a_nR(z, 800, 1600)[0].real
        a2 = a_nR(z, 400, 800)[0].real
        print(f"p={p}: lambda={lam(p):.6f}  (a_800/a_400)^(1/400)="
              f"{(a1 / a2) ** (1 / 400):.6f}")
    # shape test: second differences of f(t)=log lambda(e^t)
    ps = np.linspace(0.30, 0.995, 1400)
    t = np.log(ps)
    f = np.array([np.log(lam(p)) for p in ps])
    d2 = (f[2:] - 2 * f[1:-1] + f[:-2]) / (t[1] - t[0]) ** 2  # nonuniform t:
    # use exact nonuniform second divided differences instead
    dd = 2 * ((f[2:] - f[1:-1]) / (t[2:] - t[1:-1])
              - (f[1:-1] - f[:-2]) / (t[1:-1] - t[:-2])) / (t[2:] - t[:-2])
    neg = ps[1:-1][dd < -1e-6]
    print("min second divided difference:", dd.min(),
          "at p =", ps[1:-1][dd.argmin()])
    print("p-range with dd<0:", (neg.min(), neg.max()) if len(neg) else None)
    for p in (0.55, 0.6, 0.7, 0.8, 0.9, 0.95, 0.99):
        print(f"p={p}: mu={mu(p):.6f} lambda={lam(p):.6f}")


if __name__ == "__main__":
    main()
