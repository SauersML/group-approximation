"""Calibration: Calegari-Walker's Sapir-group certificate (phi^4, w=babaBABA, k=3) must be SAT."""
import sys, time
from sat4 import *
phi = power({"a": "ab", "b": "ba", "c": "c"}, int(sys.argv[1]))
w = sys.argv[2]; k = int(sys.argv[3])
g = gate_of(phi)
print("gates", "".join(g[d] for d in "abAB"), "len f(w)", len(apply(phi, w)), flush=True)
t0 = time.time()
B = BoundaryK(phi, w, k)
pr, it = solve4(B, g)
print("result", "SAT" if pr else pr, "iters", it, "time", round(time.time() - t0, 1), flush=True)
if pr:
    Bt, pt = lift(B, pr, w, k)
    print(verify4(Bt, pt, g, nunroll=1), flush=True)
