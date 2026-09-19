"""For a fixed gadget (integer weight per edge orbit), compare per pattern orbit:
  relaxed value  = exact min cut over auxiliary-unfolded f (Wiman relaxation; exact),
  folded value   = best folded f found by heavy heuristic search (an UPPER bound on the
                   true folded minimum, so the folded ratio printed is an upper bound on
                   the gadget's true soundness ratio, and a lower bound only if search is exact).
Ratios are K * E_xi[value] / total weight.

usage: python3 probe_gadget_gap.py k W0,W1,... [kicks]
"""
import sys, time
from fractions import Fraction
import numpy as np
from hadk_setup import setup
from hadk_mincut import unfolded_price
from hadk_fold import local_search

k = int(sys.argv[1])
Wo = np.array([int(t) for t in sys.argv[2].split(",")], dtype=np.int64)
kicks = int(sys.argv[3]) if len(sys.argv) > 3 else 60
S = setup(k)
K, N, full = S["K"], S["N"], S["full"]
half = N >> 1
cap = Wo[S["orb"]]
tot = int(cap.sum())
wE = cap.astype(np.float64)
rng = np.random.default_rng(7)
reps = np.arange(half, dtype=np.int64)
t0 = time.time()
R_rel = Fraction(0); R_fold = Fraction(0)
for q, xi in enumerate(S["reps"]):
    v_rel, _, f0 = unfolded_price(S, cap, xi)
    ft = ~f0[full ^ np.arange(N)]
    T, D = (f0 & ft)[:half], (f0 ^ ft)[:half]
    st = [f0[:half].copy(), ft[:half].copy()]
    for i in range(K):
        dic = ((reps >> i) & 1) == 0
        st += [np.where(D, dic, T), np.where(D, ~dic, T)]
    best = None
    for b0 in st:
        v, cut, b = local_search(S, wE, xi, b0)
        if best is None or v < best[0]:
            best = (v, cut, b)
    for t in range(kicks):
        p = [0.005, 0.02, 0.06][t % 3]
        b0 = best[2].copy()
        fl = rng.random(half) < p
        b0[fl] = ~b0[fl]
        v, cut, b = local_search(S, wE, xi, b0)
        if v < best[0] - 1e-9:
            best = (v, cut, b)
    v_fold = int(round(best[0]))
    wq = Fraction(int(S["psize"][q]), int(S["npat"]))
    R_rel += wq * v_rel; R_fold += wq * v_fold
    print(f"pattern orbit {q}: relaxed {v_rel}  folded(best found) {v_fold}  "
          f"ratio {v_fold / v_rel:.5f}  |D|/half {D.mean():.4f} [{time.time() - t0:.0f}s]", flush=True)
print(f"relaxed ratio (exact)            K*E[min]/tot = {float(K * R_rel / tot):.6f}")
print(f"folded ratio (best found, >= true) K*E[min]/tot = {float(K * R_fold / tot):.6f}")
