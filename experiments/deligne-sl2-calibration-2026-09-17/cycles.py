"""Lower-bound certificates for mu_t: integral 2-cycles c of the Schreier complex Y_X with kappa(c) not 0 mod 3.
Any such c gives mu_{1/3}(X) >= dist(kappa(c)/3, Z) / ||c||_1  (pair t*kappa - delta a - n with c).
Finds the minimum l1 norm of an integral cycle with kappa(c) = 1 mod 3 (ILP, scipy/HiGHS).
Usage: python3 cycles.py SETNAME [time_limit]
"""
import sys, json, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix, hstack, vstack, eye as speye
from sl2_milp import SETS, build_cells

def min_cycle(perms, tl=600, cap=60):
    A, kap, names, col = build_cells(perms)          # A: cells x edges; boundary = A^T
    m, E = A.shape
    B = A.T.tocsr()                                   # E x m
    # c = p - q, p,q >= 0 integer; kappa(c) - 3 j = 1, j integer
    Z = csr_matrix((E, 1))
    Aeq = vstack([hstack([B, -B, Z]), hstack([csr_matrix(kap), csr_matrix(-kap), csr_matrix([[-3.0]])])]).tocsr()
    beq = np.concatenate([np.zeros(E), [1.0]])
    cost = np.concatenate([np.ones(2 * m), [0]])
    lb = np.concatenate([np.zeros(2 * m), [-cap]]); ub = np.concatenate([np.full(2 * m, cap), [cap]])
    res = milp(cost, constraints=LinearConstraint(Aeq, beq, beq), integrality=np.ones(2 * m + 1),
               bounds=Bounds(lb, ub), options=dict(time_limit=tl, disp=False))
    if res.x is None:
        return dict(status=res.status, norm=None)
    c = np.round(res.x[:m] - res.x[m:2 * m]).astype(int)
    supp = [(names[i][0], int(names[i][1]), int(c[i])) for i in range(m) if c[i]]
    return dict(status=res.status, norm=int(abs(c).sum()), kappa=int(kap @ c), bound=getattr(res, "mip_dual_bound", None),
                support=supp)

if __name__ == "__main__":
    name = sys.argv[1]; tl = float(sys.argv[2]) if len(sys.argv) > 2 else 600
    t0 = time.time(); perms = SETS(name); r = min_cycle(perms, tl)
    r.update(name=name, npts=len(perms["x"]), secs=round(time.time() - t0, 1))
    print(json.dumps(r, default=float), flush=True)
