#!/usr/bin/env python3
"""Dense Z windows with every reader of the special site: E = {0,...,m-1}, F = {0,-1,...,-(m-1)}.
The Folner-loss heuristic predicts that minimal-window certificates should get harder as m grows.
usage: dense_z_large.py m [extra non-readers as comma list]
"""
import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'shannon-window-certificates-2026-09-17'))
from shannon_lp import Zd, build, solve, show
G = Zd(1)
m = int(sys.argv[1])
E = [(i,) for i in range(m)]
F = [(-i,) for i in range(m)]
if len(sys.argv) > 2 and sys.argv[2]:
    F += [(int(v),) for v in sys.argv[2].split(',')]
t0 = time.time()
d = build(G, E, F)
res, _ = solve(d)
print('Z E=%s F=%s n=%d nv=%d status=%d LP=%.6f time=%.0fs' % (show(G, E), show(G, F), d['n'], d['nv'], res.status, res.fun, time.time() - t0), flush=True)
