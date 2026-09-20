"""Calibration of census.py against the exact SL(2,9) = 2.A_6 solution found by sl2_9_irreps.py.

In the 4-dimensional faithful irreps of SL(2,9) there are exact pairs with U^4 = -1, V^3 = 1,
(VU)^5 = 1 and r_2 = 1 (r_1 defect sqrt 2). Eigen-type: U has each odd 8th root once
(angles/pi = +-1/4, +-3/4), V has angles/pi {0, 0, 2/3, -2/3} (one irrep) or {2/3, 2/3, -2/3, -2/3}
(the other). So the mode-02 twisted defect (pentagon + r_2 only) is 0 in dimension 4.
This script asks whether the census optimizer, restricted to that eigen-type, finds it.
"""
import math
import sys

import numpy as np

import census

restarts = int(sys.argv[1]) if len(sys.argv) > 1 else 64
iters = int(sys.argv[2]) if len(sys.argv) > 2 else 600
census.MODE = (0, 2)
ue = [census.U_EIG[k] for k in range(4)]
types = {"V(0,0,1,2)": [census.V_EIG[k] for k in (0, 0, 1, 2)],
         "V(1,1,2,2)": [census.V_EIG[k] for k in (1, 1, 2, 2)]}
rng = np.random.default_rng(3)
for name, ve in types.items():
    res = census.optimize_batch([(ue, ve)], restarts, iters, rng)
    print(f"mode 02, U(0,1,2,3) {name}: best defect {res[0][0]:.3e} over {restarts} restarts x {iters} iters",
          flush=True)
