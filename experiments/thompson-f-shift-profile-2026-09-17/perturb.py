"""Perturbation probe: does the support-2 ratio optimum of ratio_shift.py improve at larger support?

Seeds support L from the saved support-2 optimum h2 as h2 (x) 1^(L-2) plus Gaussian noise of size eps,
reruns the ratio optimisation, and prints the best C found.
Usage: python3 perturb.py L tau iters eps1,eps2,...
"""
import sys
import torch
import ratio_shift as rs

L, tau, iters = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
epss = [float(x) for x in sys.argv[4].split(",")]
h = torch.load(f"ratio_q2_L2_t{tau}.pt")
for _ in range(L - 2):
    h = torch.kron(h, torch.eye(2, dtype=rs.DT))
m = h.shape[0]
for eps in epss:
    for trial in range(2):
        h0 = h + eps * torch.randn(m, m, dtype=rs.DT)
        hh, r1, r2, cm = rs.optimise(h0, 2, tau, iters, lr=0.01)
        C = (cm / max(r1, r2)) ** 0.5
        print(f"L={L} tau={tau} eps={eps} trial={trial}: e(R1)={r1:.5f} e(R2)={r2:.5f} "
              f"e(c)={cm:.4f} C={C:.4f}", flush=True)
