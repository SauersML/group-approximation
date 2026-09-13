"""Exact dual certificate that kappa* = 5/17 for the Sp4(Z) root-window coboundary LP (see lp_kappa.py).
Active rows at psi_q = (1/17,1/17,0,0,-1/17,-1/17,0,0) with signs s_r = sign(<e_r,psi_q> - k_r); a vertex w >= 0 of
{sum w s e = 0, sum w = 1} on those rows, solved exactly over Q on its support, gives the matching lower bound
max_r |<e_r,psi> - k_r| >= -sum w s k = 5/17 for every psi.  FINITE-WINDOW LP FACT; not a sector lower bound."""
import json, sys
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
pres = json.load(open(sys.argv[1])); rows = {}
for r, k in zip(pres["relators"], pres["lifts"]):
    e = [0]*8
    for x in r: e[x % 8] += 1 if x < 8 else -1
    rows[tuple(e) + (int(k),)] = 1
psi = [F(1,17), F(1,17), 0, 0, F(-1,17), F(-1,17), 0, 0]; kap = F(5,17)
act = []
for u in sorted(rows):
    v = sum(F(a)*b for a, b in zip(u[:8], psi)) - u[8]
    assert abs(v) <= kap
    if abs(v) == kap: act.append((u, 1 if v > 0 else -1))
print("rows", len(rows), "exact max", kap, "active rows", len(act), flush=True)
Mf = np.array([[s*a for a in u[:8]] for u, s in act], dtype=float).T
Aeq = np.vstack([Mf, np.ones((1, len(act)))]); beq = np.concatenate([np.zeros(8), [1.0]])
res = linprog(np.zeros(len(act)), A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*len(act), method="revised simplex")
print("vertex status", res.status, res.message, flush=True)
supp = [j for j in range(len(act)) if res.x[j] > 1e-10]
print("support size", len(supp), flush=True)
# exact solve on the support: 9 equations, |supp| unknowns
A = [[F(s*u[i]) for (u, s) in (act[j] for j in supp)] for i in range(8)] + [[F(1)]*len(supp)]
b = [F(0)]*8 + [F(1)]
# Gaussian elimination to reduced row echelon form
m, n = len(A), len(supp); Aug = [A[i] + [b[i]] for i in range(m)]; piv = []; row = 0
for col in range(n):
    p = next((i for i in range(row, m) if Aug[i][col] != 0), None)
    if p is None: continue
    Aug[row], Aug[p] = Aug[p], Aug[row]; pv = Aug[row][col]; Aug[row] = [x/pv for x in Aug[row]]
    for i in range(m):
        if i != row and Aug[i][col] != 0:
            f = Aug[i][col]; Aug[i] = [a - f*c for a, c in zip(Aug[i], Aug[row])]
    piv.append(col); row += 1
    if row == m: break
w = [F(0)]*n
for i, col in enumerate(piv): w[col] = Aug[i][n]
ok = all(sum(A[i][j]*w[j] for j in range(n)) == b[i] for i in range(m)) and all(x >= 0 for x in w)
lb = -sum(w[j]*act[supp[j]][1]*act[supp[j]][0][8] for j in range(n))
print("exact system satisfied and w >= 0:", ok, "; lower bound -sum w s k =", lb, flush=True)
for j in range(n):
    u, s = act[supp[j]]; print(f"  s {s:+d} e {list(u[:8])} k {u[8]} w {w[j]}", flush=True)
print("KAPPA* EXACT = 5/17" if ok and lb == kap else "certificate not exact", flush=True)
print("DONE", flush=True)
