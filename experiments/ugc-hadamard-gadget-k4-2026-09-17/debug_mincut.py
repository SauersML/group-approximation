"""sanity check of unfolded_price at small k."""
import sys
import numpy as np
from hadk_setup import setup
from hadk_mincut import unfolded_price, pins

k = int(sys.argv[1]) if len(sys.argv) > 1 else 2
S = setup(k)
cap = np.ones(S["E"], dtype=np.int64)
for q, xi in enumerate(S["reps"]):
    v, cut, f = unfolded_price(S, cap, xi)
    pv = pins(S, xi)
    print(q, int(xi), "flow", v, "cut", int(cut.sum()), "f+", int(f.sum()),
          "pins ok", all(bool(f[m]) == bool(val) for m, val in pv))
