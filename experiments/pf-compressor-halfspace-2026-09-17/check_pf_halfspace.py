"""Checks for (Q1) of perron-frobenius-compressors-cannot-close-the-level-class.

sigma = [[1,1,0],[0,1,1],[1,1,1]] in SL_3(Z), nonnegative and primitive.
theta = Perron-Frobenius eigenvector of sigma^T, P_theta = {p : <theta,p> > 0} u {0}.
Checks, exactly where possible:
  1. det sigma = 1, sigma >= 0, sigma^2 > 0 (primitive);
  2. char poly irreducible over Q, so lambda is irrational and the ray of theta is irrational;
  3. theta > 0, so N^3 \ 0 lies in P_theta (U_1 <= E_theta);
  4. sigma(P_theta) = P_theta (sign of <theta, sigma p> = sign of <theta, p>);
  5. sigma^-1 is not nonnegative: sigma^-1 C sigma is not inside Gamma (C not normal);
  6. every p in P_theta \ 0 with |p|_inf <= 6 has sigma^n p in N^3 for some n <= 40
     (infranormality: sigma-hat^n(g) is polynomial for n large);
  7. no negative monomial ray -j m (m in N^3 \ 0) meets P_theta, and no sigma-orbit of a
     point of P_theta meets one (all orbit points keep <theta, .> > 0).
Run: python3 check_pf_halfspace.py   (exit 0 = all checks pass)
"""
import itertools
import sys

import sympy as sp

S = sp.Matrix([[1, 1, 0], [0, 1, 1], [1, 1, 1]])
x = sp.symbols("x")
ok = True


def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    ok = ok and bool(cond)


check("det sigma = 1", S.det() == 1)
check("sigma nonnegative", all(e >= 0 for e in S))
check("sigma^2 positive (primitive)", all(e > 0 for e in S**2))
cp = S.charpoly(x).as_expr()
print("char poly:", sp.factor(cp))
check("char poly irreducible over Q", sp.Poly(cp, x).is_irreducible)

# Perron-Frobenius data (exact algebraic numbers)
lam = max(sp.Poly(cp, x).nroots(n=50), key=lambda r: sp.re(r))
lam = sp.re(lam)
ST = S.T
# theta: kernel of (S^T - lam I), computed numerically to 50 digits
M = (ST - lam * sp.eye(3)).evalf(50)
theta = M.nullspace(simplify=False)
if not theta:
    # fall back to power iteration
    v = sp.Matrix([1, 1, 1])
    for _ in range(200):
        v = ST * v
        v = v / max(v)
    theta = v.evalf(50)
else:
    theta = theta[0]
theta = theta / max(theta, key=abs)
theta = sp.Matrix([sp.N(t, 40) for t in theta])
print("lambda =", sp.N(lam, 20), " theta =", [sp.N(t, 12) for t in theta])
check("theta > 0", all(t > 0 for t in theta))
check("sigma^T theta = lambda theta", max(abs(e) for e in (ST * theta - lam * theta)) < 1e-30)


def pair(p):
    return sum(theta[i] * p[i] for i in range(3))


Sinv = S.inv()
check("sigma^-1 integral", all(e == int(e) for e in Sinv))
check("sigma^-1 has a negative entry (C not normal)", any(e < 0 for e in Sinv))
print("sigma^-1 e_1 =", list(Sinv[:, 0]))

box = [p for p in itertools.product(range(-6, 7), repeat=3) if any(p)]
inv_ok = all((pair(S * sp.Matrix(p)) > 0) == (pair(p) > 0) for p in box)
check("sigma preserves P_theta on the box", inv_ok)

worst = 0
reach_ok = True
for p in box:
    if pair(p) <= 0:
        continue
    v = sp.Matrix(p)
    for n in range(41):
        if all(e >= 0 for e in v):
            worst = max(worst, n)
            break
        v = S * v
    else:
        reach_ok = False
check("sigma^n p in N^3 for n <= 40, all p in P_theta of the box (max n = %d)" % worst, reach_ok)

neg_ok = all(pair(p) < 0 for p in itertools.product(range(0, 7), repeat=3) if any(p)
             for p in [tuple(-e for e in p)])
check("negative monomial rays miss P_theta", neg_ok)

orbit_ok = True
for p in box:
    if pair(p) <= 0:
        continue
    v = sp.Matrix(p)
    for n in range(12):
        if all(e <= 0 for e in v):
            orbit_ok = False
        v = S * v
check("sigma-orbits of P_theta never enter -N^3", orbit_ok)

sys.exit(0 if ok else 1)
