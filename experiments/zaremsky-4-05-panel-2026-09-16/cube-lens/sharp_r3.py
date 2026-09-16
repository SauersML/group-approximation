"""Recompute the R^3 l1 sharpness example of artifact section 10."""
import itertools
import numpy as np
from scipy.optimize import linprog
Z = [(0,-1,-1), (-2,0,-2), (-1,1,0), (1,1,-2)]
rho = [2.5, 2.5, 2.5, 2.0]
def f(idx):
    # min t s.t. |p - z_i|_1 - rho_i <= t ; variables p(3), e_i(3 per i), t
    I = list(idx); n = 3 + 3*len(I) + 1
    A=[]; b=[]
    for j,i in enumerate(I):
        for c in range(3):
            e = 3 + 3*j + c
            r = np.zeros(n); r[c]=1; r[e]=-1; A.append(r); b.append(Z[i][c])
            r = np.zeros(n); r[c]=-1; r[e]=-1; A.append(r); b.append(-Z[i][c])
        r = np.zeros(n); r[3+3*j:3+3*j+3]=1; r[-1]=-1; A.append(r); b.append(rho[i])
    cv = np.zeros(n); cv[-1]=1
    res = linprog(cv, A_ub=np.array(A), b_ub=np.array(b), bounds=[(None,None)]*n, method='highs')
    return res.fun
full = f(range(4)); sub = max(f(T) for T in itertools.combinations(range(4),3))
print('full', full, 'max3', sub, 'gap', full-sub)
