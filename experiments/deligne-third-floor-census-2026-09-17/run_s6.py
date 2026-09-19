"""Exact MILP mu(X) on S6 = Sp_4(F_2)-sets (Weierstrass-point model, a_i -> (i-1,i)).
Usage: python3 run_s6.py NAME [time_limit]"""
import sys, json, time
from census import *
from fractions import Fraction

SETS = {
    "s6_1": lambda: X_s6_tuples(1),                               # 6, stabilizer S5
    "s6_2": lambda: X_s6_tuples(2),                               # 30, S4
    "s6_3": lambda: X_s6_tuples(3),                               # 120, S3
    "s6_4": lambda: X_s6_tuples(4),                               # 360, S2
    "s6_5": lambda: X_s6_tuples(5),                               # 720, regular
    "s6_pair": lambda: X_s6_partition([(0, 1), (2, 3, 4, 5)]),    # 15, S2xS4
    "s6_33": lambda: X_s6_partition([(0, 1, 2), (3, 4, 5)]),      # 10
    "s6_33ord": lambda: X_s6_partition([(0, 1, 2), (3, 4, 5, 9)]),  # 20 (block with dummy 9 marks it)
    "s6_222": lambda: X_s6_partition([(0, 1), (2, 3), (4, 5)]),   # 15, synthemes
    "s6_2_4ord": lambda: X_s6_partition([(0, 1), (2,), (3, 4, 5)]),  # 60
}
if __name__ == "__main__":
    name = sys.argv[1]; tl = float(sys.argv[2]) if len(sys.argv) > 2 else 600
    perms, _ = SETS[name]()
    t0 = time.time()
    r = mu_milp(perms, tl)
    eps = r["eps"]
    out = dict(name=name, npts=len(perms[0]), cells=r["cells"], status=r["status"], msg=r["msg"],
               eps=eps, dual_bound=r["bound"], eps_times_291=None if eps is None else eps * 291,
               frac=None if eps is None else str(Fraction(eps).limit_denominator(100000)), secs=time.time() - t0)
    print(json.dumps(out, default=float), flush=True)
