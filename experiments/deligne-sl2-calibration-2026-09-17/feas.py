"""Feasibility form of the mu_t MILP: is there a model with defect <= cap, for cap just below the Kahler value 1/51?
An 'infeasible' verdict from HiGHS is a (numerical) proof that mu_(1/3)(X) > cap.
Usage: python3 feas.py SETNAME cap time_limit
"""
import sys, json, time
from sl2_milp import SETS, mu_milp

name, cap, tl = sys.argv[1], float(sys.argv[2]), float(sys.argv[3])
t0 = time.time(); perms = SETS(name)
r = mu_milp(perms, 1 / 3, tl, eps_cap=cap)
print(json.dumps(dict(name=name, npts=len(perms["x"]), cap=cap, status=int(r["status"]), msg=r["msg"],
                      eps=None if r["eps"] is None else float(r["eps"]), secs=round(time.time() - t0, 1))), flush=True)
