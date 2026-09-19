"""Minimax LP over mixtures of H_t, reading halfcube_price.c output.

usage: python3 lp_file.py k prices.txt [q_0 ... q_{K/2-1}]
With q given, prints the max price of that fixed mixture instead.
"""
import sys
import numpy as np
from scipy.optimize import linprog

FLOAT = "--float" in sys.argv  # input from halfcube_price_ld.c (unscaled)
QOUT = [a[7:] for a in sys.argv if a.startswith("--qout=")]  # write optimal q here
sys.argv = [a for a in sys.argv if a != "--float" and not a.startswith("--qout=")]
k = int(sys.argv[1])
K = 1 << k
if FLOAT:
    V = np.unique(np.round(np.loadtxt(sys.argv[2], ndmin=2), 13), axis=0)
else:
    # exact integers scaled by 2^K (may exceed int64 at k = 6)
    rows = {tuple(int(v) for v in line.split()) for line in open(sys.argv[2]) if line.strip()}
    V = np.array([[v / float(1 << K) for v in r] for r in sorted(rows)])
if len(sys.argv) > 3:
    q = np.array([float(s) for s in sys.argv[3:]])
    q /= q.sum()
    p = V @ q
    print("classes", len(V), "max price of given mixture", p.max())
    print("worst class", V[p.argmax()])
    sys.exit()
n, T = V.shape
c = np.zeros(T + 1)
c[-1] = 1
A = np.hstack([V, -np.ones((n, 1))])
res = linprog(c, A_ub=A, b_ub=np.zeros(n), A_eq=[[1] * T + [0]], b_eq=[1],
              bounds=[(0, None)] * T + [(None, None)], method="highs")
print("k", k, "classes", n, "LP value", res.x[-1])
print("q", " ".join("%.5f" % v for v in res.x[:T]))
if QOUT:
    with open(QOUT[0], "w") as fh:
        fh.write(" ".join("%.15g" % max(v, 0.0) for v in res.x[:T]) + "\n")
