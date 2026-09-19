"""Does dimension help inside the ratio-1:2 sector?  Seed = (witness_O3E3E3) (+) extra exact tokens, then optimise.
If the n = 12 witness were a dead end, the optimum of witness (+) witness would stay at 0.132648 (direct sum).
Run: python3 refine_witness.py "<extra tokens or W>" noise seed steps     e.g. python3 refine_witness.py "W" 0.2 0 400
"""
import math, sys
import numpy as np
from scipy.linalg import block_diag
import match

th = math.pi / 3
extra, noise, seed, steps = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
w = np.load("witness_O3E3E3.npz")
blocks = [[w[k] for k in "srSR"]]
for t in extra.split():
    blocks.append([w[k] for k in "srSR"] if t == "W" else match.seed_blocks([t]))
mats = [block_diag(*[b[k] for b in blocks]).astype(complex) for k in range(4)]
d, (s, r, S, R) = match.solve_seeded(mats, th, seed, noise, steps)
n = s.shape[0]
I = np.eye(n)
nrm = lambda A: float(np.linalg.norm(A, 2))
rel = max(nrm(s @ s - I), nrm(S @ S - I), nrm(r @ r @ r - I), nrm(R @ R @ R - I))
print(f"witness(+)[{extra}] n={n} noise={noise} seed={seed} steps={steps} relator_error={rel:.1e} delta={d:.6f} "
      f"w={match.windings(s, r, S, R, th)}", flush=True)
