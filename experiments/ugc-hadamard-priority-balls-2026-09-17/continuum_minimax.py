"""Exploratory minimax over radius profiles for the continuum priority-ball model
(see continuum_explore.py).  Cutting-plane loop: optimize the profile against a
pool of worst configurations, then search for a new worst configuration.
Floating point; proves nothing.
"""
import sys
import numpy as np
from scipy.optimize import minimize
from continuum_explore import make_profile, cost, worst

smax = float(sys.argv[1]) if len(sys.argv) > 1 else 0.4
n = int(sys.argv[2]) if len(sys.argv) > 2 else 10
rounds = int(sys.argv[3]) if len(sys.argv) > 3 else 12


def prof(w):
    w = np.abs(w) + 1e-9
    c = np.cumsum(w) / np.sum(w)
    vals = 1 - c[:-1]
    return make_profile(smax, vals)


w = np.ones(n + 1)
pool = [np.array([s]) for s in np.linspace(0, smax, 25)]
for it in range(rounds):
    def obj(v):
        return v[-1]
    cons = [{'type': 'ineq',
             'fun': (lambda v, p=p: v[-1] - cost(p, *prof(v[:-1])))} for p in pool]
    v0 = np.concatenate([w, [max(cost(p, *prof(w)) for p in pool)]])
    r = minimize(obj, v0, method='SLSQP', constraints=cons,
                 bounds=[(1e-6, None)] * (n + 1) + [(0, None)],
                 options={'maxiter': 400})
    w = r.x[:-1]
    g, a = prof(w)
    wc, cfg = worst(g, a, smax, Mmax=9, starts=6)
    print(f"round {it}: pool-max={r.x[-1]:.4f} true-worst={wc:.4f} cfg={np.round(cfg,3)}", flush=True)
    pool.append(cfg)
xs = np.linspace(0, smax, n + 2)
print("profile g on grid:", np.round(g(xs), 4))
