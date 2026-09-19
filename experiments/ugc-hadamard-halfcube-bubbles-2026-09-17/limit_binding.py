"""Which configurations bind in the limit-model LP (limit_model_lp.py).

usage: python3 limit_binding.py mmax h
Prints the LP value, the optimal gamma, and for each binding row (positive
dual) the configuration: its pin distances and the edge pattern u.
"""
import sys
import numpy as np
from scipy.optimize import linprog
from limit_model_lp import Cells, boolean_configs, fractional_configs, coef_rows

mmax, h = int(sys.argv[1]), float(sys.argv[2])
cells = Cells(h, 0.0)
configs, labels = [], []
for m in range(mmax + 1):
    for cfg in boolean_configs(m):
        configs.append(cfg)
        labels.append("bool m=%d" % m)
for cfg in fractional_configs(0, [1 - 2 * c for c in cells.centres]):
    configs.append(cfg)
    labels.append("single fractional pin")
rows, owner = [], []
for idx, cfg in enumerate(configs):
    r = coef_rows([cfg], cells)
    rows.append(r)
    owner += [(idx, ui) for ui in range(len(r))]
rows = np.vstack(rows)
n = len(cells.centres)
c = np.zeros(n + 1)
c[-1] = 1
A = np.hstack([rows, -np.ones((len(rows), 1))])
widths = cells.hi - cells.lo
res = linprog(c, A_ub=A, b_ub=-np.ones(len(rows)), A_eq=[list(widths) + [0]], b_eq=[1],
              bounds=[(0, None)] * n + [(None, None)], method="highs")
print("LP value", res.x[-1])
print("gamma", " ".join("%.3f" % v for v in res.x[:n]))
duals = -res.ineqlin.marginals
shown = set()
for r in np.argsort(-duals):
    if duals[r] < 1e-9:
        break
    idx, ui = owner[r]
    pins, pts = configs[idx]
    key = (tuple(sorted(round(d, 4) for d, _ in pins)), labels[idx])
    if key in shown:
        continue
    shown.add(key)
    print("dual %.4f  %s  pin distances %s  u-index %d" % (duals[r], labels[idx], key[0], ui))
