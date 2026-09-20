"""Reproduce and certify a theta = pi/3 matching below the scalar profile 2 sin(pi/36) = 0.17431.

Seed "O3 E3 E3" (n = 12: odd theta = pi part of the SL_2(F_3) permutation rep, dim 4, plus two copies of the even
theta = 0 part, dim 4 each; the determinant bound of this winding sector is 0).  Optimise with match.solve_seeded,
then certify in float64 numpy: s^2 = S^2 = 1, r^3 = R^3 = 1, unitarity, and the operator-norm defect delta.
Saves the witness to witness_O3E3E3.npz.  Run: python3 verify_below_profile.py [seed noise steps]
"""
import math, sys
import numpy as np
import match

th = math.pi / 3
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
noise = float(sys.argv[2]) if len(sys.argv) > 2 else 0.5
steps = int(sys.argv[3]) if len(sys.argv) > 3 else 250
spec = sys.argv[4] if len(sys.argv) > 4 else "O3 E3 E3"
mats = match.seed_blocks(spec.split())
d, (s, r, S, R) = match.solve_seeded(mats, th, seed, noise, steps)
n = s.shape[0]
I = np.eye(n)
g = complex(math.cos(-th / 6), math.sin(-th / 6))
nrm = lambda A: float(np.linalg.norm(A, 2))
rel = max(nrm(s @ s - I), nrm(S @ S - I), nrm(r @ r @ r - I), nrm(R @ R @ R - I),
          max(nrm(M.conj().T @ M - I) for M in (s, r, S, R)))
dT = nrm(S @ R - g * (s @ r) @ (s @ r))
Li = S @ R.conj().T
dU = nrm(s @ r.conj().T - (1 / g) * Li @ Li)
print(f"spec=[{spec}] n={n} seed={seed} noise={noise} steps={steps} relator_error={rel:.2e} "
      f"dT={dT:.6f} dU={dU:.6f} delta={max(dT, dU):.6f} profile=2sin(pi/36)={2*math.sin(math.pi/36):.6f} "
      f"w={match.windings(s, r, S, R, th)}", flush=True)
np.savez_compressed(f"witness_{spec.replace(' ', '')}.npz", s=s, r=r, S=S, R=R)
