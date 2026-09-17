#!/usr/bin/env python3
"""Exact (sympy) check of the scalar core of the post-selection proof (w3-stab referee).
Not a Lean verification."""
import sympy as sp
s2 = sp.sqrt(2); c = 1/s2; t = s2 - 1
M, lam, a, wR, W, WA = sp.symbols('M lambda a w_R W W_A', real=True)
checks = {
  "t = c/(1+c)": sp.simplify(c/(1+c) - t) == 0,
  "(1+c) t = c": sp.simplify((1+c)*t - c) == 0,
  "(1-t)/sqrt2 = t": sp.simplify((1-t)/s2 - t) == 0,
  "(1-t^2)/(1+t^2) = 1/sqrt2": sp.simplify((1-t**2)/(1+t**2) - c) == 0,
  "tan(pi/8) = sqrt2-1": sp.simplify(sp.tan(sp.pi/8) - t) == 0,
  # Step 4 expansion: w_R + (1+c)(lam - a/(1+M) - w_R) - c(W - w_R - W_A) = (1+c)lam - cW + [c W_A - (1+c)a/(1+M)]
  "Step-4 algebra": sp.simplify(wR + (1+c)*(lam - a/(1+M) - wR) - c*(W - wR - WA)
                                - ((1+c)*lam - c*W + (c*WA - (1+c)*a/(1+M)))) == 0,
  # identity (2): (lam - a + lam M)/(1+M) = lam - a/(1+M)
  "energy formula (2)": sp.simplify((lam - a + lam*M)/(1+M) - (lam - a/(1+M))) == 0,
}
# F2 branch 1: on [0, 1/sqrt2], t(1+M) - M is affine, so nonnegative iff nonnegative at endpoints
g = t*(1+M) - M
checks["F2 branch 1 (endpoints)"] = bool(sp.simplify(g.subs(M, 0)) >= 0) and sp.simplify(g.subs(M, c)) == 0
# F2 branch 2: on [1/sqrt2, 1], t^2(1+M)^2 - (1-M^2) = (1+M)(t^2(1+M) - (1-M)); second factor affine increasing, zero at 1/sqrt2
h = t**2*(1+M) - (1-M)
checks["F2 branch 2 factorization"] = sp.expand(t**2*(1+M)**2 - (1-M**2) - (1+M)*h) == 0
checks["F2 branch 2 root at 1/sqrt2"] = sp.simplify(h.subs(M, c)) == 0
checks["F2 branch 2 slope > 0"] = bool(sp.simplify(sp.diff(h, M)) > 0)
# sharpness example
lamX = s2/2; stabX = sp.Rational(1, 2)
checks["(X+Z)/2 tight"] = sp.simplify(lamX - stabX - c*(1 - lamX)) == 0
for k, v in checks.items():
    print(f"{k}: {v}")
print("RESULT:", "all exact checks pass" if all(checks.values()) else "FAILURE")
