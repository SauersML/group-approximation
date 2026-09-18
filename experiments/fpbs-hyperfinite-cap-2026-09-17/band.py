"""Band trigger and stage bound for fpbs-kazhdan-hyperfinite-connection-cap.

theta = 1 - kappa^2/2 is the cap on min_s tau^E(s)/p for a hyperfinite E.
f_p(t) = 2 q t - q^2 p t^2 is the union-step lower bound, q = 1/(1+sqrt(1-p)).
t_* = (1 - sqrt(1 - p theta)) / (1 - sqrt(1 - p)) solves f_p(t_*) = theta.
n_0 = min{n : f_p^n(p) > theta} bounds the first non-hyperfinite exact stage by n_0 + 1.

Checks (exact arithmetic where possible, floats elsewhere):
  1. f_p(t_*) = theta, and t_* < theta (strict convexity of 1 - sqrt(1-x)).
  2. (theta - t_*)/theta ~ p kappa^2 / 8 as p -> 0.
  3. n_0 against the estimate (4/p) log(theta/p).
Run: nice -n 10 timeout 1200 python3 band.py
"""
import math


def q_of(p):
    return 1.0 / (1.0 + math.sqrt(1.0 - p))


def f(p, t):
    q = q_of(p)
    return 2 * q * t - q * q * p * t * t


def t_star(p, theta):
    return (1 - math.sqrt(1 - p * theta)) / (1 - math.sqrt(1 - p))


def n0(p, theta):
    t, n = p, 0
    while t <= theta:
        t = f(p, t)
        n += 1
        if n > 10**8:
            return None
    return n


def main():
    ok = True
    for kappa in (0.05, 0.2, 0.5, 1.0):
        theta = 1 - kappa * kappa / 2
        for p in (0.3, 0.1, 0.01, 0.001):
            ts = t_star(p, theta)
            err = abs(f(p, ts) - theta)
            rel = (theta - ts) / theta
            pred = p * kappa * kappa / 8
            n = n0(p, theta)
            est = 4 / p * math.log(theta / p)
            print(f"kappa={kappa:<5} p={p:<6} t*={ts:.8f} |f(t*)-theta|={err:.1e} "
                  f"rel_width={rel:.3e} p*kappa^2/8={pred:.3e} n0={n} est={est:.0f}")
            ok &= err < 1e-12 and 0 < ts < theta
            if p <= 0.01:
                ok &= abs(rel / pred - 1) < 0.02
    print("ALL CHECKS PASS" if ok else "CHECK FAILED")


if __name__ == "__main__":
    main()
