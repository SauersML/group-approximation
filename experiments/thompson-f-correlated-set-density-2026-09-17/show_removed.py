#!/usr/bin/env python3
"""List the class windows removed by the optimal context set (height_contexts.py)."""
import sys
import numpy as np
sys.path.insert(0, '.')
from height_contexts import setup, build, densest  # noqa: E402

k, H, J, l, r = (int(x) for x in sys.argv[1:6])
R, cls, om, W = setup(k, H, J)
w, eu, ev, ec, idx = build(om, W, l, r)
full = 2 * ec.sum() / w.sum()
g, mask = densest(w, eu, ev, ec)
print('R=%.6f classes=%s omegas=%s  BB=%.6f best=%.6f' % (R, [(c[0], c[-1]) for c in cls], np.round(om, 4), full, g))
nc = len(cls)
L = l + 1 + r
lab = '0123456789abcdefghijklmnopqrstuvwxyz'
rem = np.where(~mask & (w > 0))[0]
tot = 0
for v in rem:
    t = np.unravel_index(v, (nc,) * L)
    s = ''.join(lab[x] for x in t)
    tot += w[v]
    print(s[:l] + '[' + s[l] + ']' + s[l + 1:], '%.3e' % w[v])
print('removed windows %d, removed mass %.6f' % (len(rem), tot))
