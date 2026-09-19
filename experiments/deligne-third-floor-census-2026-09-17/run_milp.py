"""Exact MILP census of mu(X) on a list of Sp_4(Z)-sets.  Usage: python3 run_milp.py NAME [time_limit]"""
import sys, json, time
from census import *
from fractions import Fraction

E1, E2, F1, F2 = (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)
def lag_canon(p): return span_canon_p(p)
SETS = {
    "point": lambda: ([np.array([0])] * 5, None),
    "P3F2": lambda: X_proj(2),
    "LagF2": lambda: X_subspace(2, [E1, E2], span_canon_p(2)),
    "P3F3": lambda: X_proj(3),
    "LagF3": lambda: X_subspace(3, [E1, E2], span_canon_p(3)),
    "F3vec": lambda: X_vectors(3),
    "F2pair_hyp": lambda: X_tuple(2, [E1, F1]),          # ordered hyperbolic pairs over F_2
    "F2pair_iso": lambda: X_tuple(2, [E1, E2]),          # ordered isotropic pairs over F_2
    "Z4vec": lambda: X_vectors(4),
    "P3F5": lambda: X_proj(5),
    "F2frame": lambda: X_tuple(2, [E1, F1, E2, F2]),      # regular S6 = Sp_4(F_2)
    "F5vec": lambda: X_vectors(5),
    "P3F7": lambda: X_proj(7),
    "Z4proj": lambda: X_subspace(4, [E1], lambda B: (min(tuple((u * x) % 4 for x in B[0]) for u in (1, 3)),)),
    "Z8proj": lambda: X_subspace(8, [E1], lambda B: (min(tuple((u * x) % 8 for x in B[0]) for u in (1, 3, 5, 7)),)),
    "Z5proj_pair": lambda: product_X(X_proj(5), X_proj(5)),
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
