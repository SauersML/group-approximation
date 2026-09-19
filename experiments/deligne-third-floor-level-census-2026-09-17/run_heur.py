import sys
import time
import numpy as np
from defect import mu, defect_of
from heur import Problem
from run_small import SETS

theta = eval(sys.argv[2]) if len(sys.argv) > 2 else 1 / 3
starts = int(sys.argv[3]) if len(sys.argv) > 3 else 10
pt = [[0] for _ in range(5)]
u0, _, b0 = mu(pt, theta, time_limit=60)
print(f"pt: mu={u0} 1/mu={1/u0}", flush=True)
for name in sys.argv[1].split(','):
    X = SETS[name]()
    n = len(X[0])
    P = Problem(X, theta)
    kahler = np.tile(b0, n)  # pulled-back model: a(x,i) = b_i
    kv = defect_of(X, theta, kahler)
    t = time.time()
    a1, t1 = P.lp_polish(kahler)
    v1 = defect_of(X, theta, a1)
    best, a = P.search(starts=starts, seed=1)
    print(f"{name} |X|={n} kahler_pullback={kv:.8f} polish_from_kahler={v1:.8f} "
          f"random_search_best={best:.8f} ratio_to_pt={min(v1,best)/u0:.4f} secs={time.time()-t:.1f}",
          flush=True)
