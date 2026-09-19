"""Exact rational lower-bound certificate for the half-cube family LP.

usage: python3 cert_dual.py k prices.txt target_num target_den

prices.txt is integer output of halfcube_price.c (prices K*Pr[cut] scaled
by 2^K; exact for k <= 5).  A certificate is a probability vector y on edge
classes with  sum_c y_c C_c(t) >= target  for every radius t.  Then every
mixture q of H_t has  max_c q.C_c >= y.(Cq) = sum_t q_t (y.C)(t) >= target,
so the family optimum is >= target.  The script finds y from the numerical
dual, then re-solves the tight system in exact rationals and verifies.
"""
import sys
from fractions import Fraction
import numpy as np
import sympy
from scipy.optimize import linprog

k = int(sys.argv[1])
K = 1 << k
target = Fraction(int(sys.argv[3]), int(sys.argv[4]))
rows = sorted({tuple(int(v) for v in line.split()) for line in open(sys.argv[2]) if line.strip()})
V = np.array(rows, dtype=float) / float(1 << K)
n, T = V.shape
# dual: max z s.t. y^T V >= z (each t), sum y = 1, y >= 0
c = np.zeros(n + 1)
c[-1] = -1
A = np.hstack([-V.T, np.ones((T, 1))])
res = linprog(c, A_ub=A, b_ub=np.zeros(T), A_eq=[[1] * n + [0]], b_eq=[1],
              bounds=[(0, None)] * n + [(None, None)], method="highs")
print("numerical dual value", -res.fun)
S = [i for i in range(n) if res.x[i] > 1e-9]
val = V[S].T @ res.x[S]
tight = [t for t in range(T) if val[t] < -res.fun + 1e-9]
print("support classes", len(S), "tight radii", tight)
scale = Fraction(1, 1 << K)
C = [[Fraction(rows[i][t]) * scale for t in range(T)] for i in S]
# exact solve: sum_i y_i C_i(t) = target on tight t, sum y = 1
ys = sympy.symbols("y0:%d" % len(S))
eqs = [sum(ys[a] * sympy.Rational(C[a][t].numerator, C[a][t].denominator) for a in range(len(S)))
       - sympy.Rational(target.numerator, target.denominator) for t in tight]
eqs.append(sum(ys) - 1)
sol = sympy.solve(eqs, ys, dict=True)
if not sol:
    sys.exit("no exact solution on the tight system")
sol = sol[0]
free = [s for s in ys if s not in sol]
# fix free variables at the rationalized numerical values
subs = {s: sympy.Rational(Fraction(float(res.x[S[ys.index(s)]])).limit_denominator(10 ** 6)) for s in free}
y = [sympy.nsimplify(sol.get(s, s).subs(subs)) if s in sol else subs[s] for s in ys]
y = [Fraction(int(sympy.fraction(v)[0]), int(sympy.fraction(v)[1])) for v in y]
assert sum(y) == 1, "weights do not sum to 1"
assert all(v >= 0 for v in y), "negative weight"
worst = min(sum(y[a] * C[a][t] for a in range(len(S))) for t in range(T))
print("exact certificate: min_t y.C(t) =", worst, ">= target", target, ":", worst >= target)
for a in range(len(S)):
    print("  weight", y[a], "class", rows[S[a]])
