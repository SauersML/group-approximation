import sys, numpy as np
from ords import levelperms, order
name, n = sys.argv[1], int(sys.argv[2]); ws = sys.argv[3:]
P = levelperms(name, n)
for w in ws:
    p = np.arange(3**n)
    for a in w: p = P[int(a)][p]
    print(w, [order(p[::3**(n-k)]//3**(n-k)) for k in range(n-2, n+1)], flush=True)
