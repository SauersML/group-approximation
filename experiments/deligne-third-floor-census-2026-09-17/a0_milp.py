"""Minimal mass A_0(X) of a detecting integral 2-cycle on Y_X: min ||S||_1, dS = 0, kappa(S) = 1 mod 3.
Character (single-cycle) lower bound LB(X) = 1/(3 A_0(X)) <= mu(X).  Compare with the exact mu(X) of run_milp/run_s6.
Usage: python3 a0_milp.py NAME [time_limit]"""
import sys, json, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import hstack, vstack, csr_matrix
from census import build_cells
import run_milp, run_s6

SETS = dict(run_milp.SETS); SETS.update(run_s6.SETS)

def a0_milp(perms, time_limit=600, cap=2000, q=3):
    """q=3: detecting cycles (kappa = 1 mod 3). q=2: D(Lambda)=1 iff an integral cycle has odd kappa."""
    A, kap, _ = build_cells(perms)
    m, E = A.shape
    At = A.T.tocsr()
    # vars p (m), q (m), t (1): At(p-q)=0 ; kap.(p-q) - 3t = 1 ; min sum p+q
    Z = csr_matrix((E, 1))
    C1 = hstack([At, -At, Z])
    k = csr_matrix(kap.reshape(1, -1).astype(float))
    C2 = hstack([k, -k, csr_matrix(np.array([[-float(q)]]))])
    C = vstack([C1, C2]).tocsr()
    lo = np.concatenate([np.zeros(E), [1.0]]); hi = lo.copy()
    cost = np.concatenate([np.ones(2 * m), [0.0]])
    kmax = float(max(1, np.abs(kap).max()))
    res = milp(cost, constraints=LinearConstraint(C, lo, hi), integrality=np.ones(2 * m + 1),
               bounds=Bounds(np.concatenate([np.zeros(2 * m), [-cap * kmax]]),
                             np.concatenate([np.full(2 * m, cap), [cap * kmax]])),
               options=dict(time_limit=time_limit, disp=False))
    return dict(status=res.status, msg=res.message, A0=None if res.x is None else res.fun,
                bound=getattr(res, "mip_dual_bound", None), cells=m)

if __name__ == "__main__":
    name = sys.argv[1]; tl = float(sys.argv[2]) if len(sys.argv) > 2 else 600
    q = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    perms, _ = SETS[name]()
    t0 = time.time()
    r = a0_milp(perms, tl, q=q)
    r.update(name=name, q=q, npts=len(perms[0]), secs=time.time() - t0,
             LB=None if (q != 3 or not r["A0"]) else 1 / (3 * r["A0"]))
    print(json.dumps(r, default=float), flush=True)
