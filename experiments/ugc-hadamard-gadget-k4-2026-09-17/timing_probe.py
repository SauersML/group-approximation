"""Timing probe for the pricing MILP: uniform edge weights, first pattern orbits."""
import sys, time
import numpy as np
from hadk_setup import setup
from hadk_price import price

k = int(sys.argv[1])
nrep = int(sys.argv[2]) if len(sys.argv) > 2 else 3
S = setup(k)
print("orbit sizes", S["osize"].tolist())
w = np.ones(S["E"]) / S["E"]
for q, xi in enumerate(S["reps"][:nrep]):
    t = time.time()
    v, lb, cut, b = price(S, w, xi, time_limit=300)
    print(q, int(xi), "val*K", v * S["K"], "lb*K", lb * S["K"], "t %.1f" % (time.time() - t), flush=True)
