# Checks for the solvable-by-metabelian edge collapse (2026-09-17, sw-053b)

These scripts support `solvable-by-metabelian-edge-images-collapse-higman-quotients`. The proof in
`higman-solvable-by-metabelian-edge-collapse-proof` does not depend on them.

- `identities.g` (GAP 4, `gap -q identities.g`; output in `identities-output.txt`) checks the two
  free-group identities used in Step 2 of the proof:
  1. `(g z)^2 = g^2 · z^g · z`, which gives `phi(z) = gamma^(2-2^P) · z^gamma z`;
  2. with `k = h u^-1`: `[w,k] = [w,u^-1] · [w,h]^(u^-1)`, which is the commutator estimate for `[w, gamma^e]`.
- `heisenberg_example.py` (`python3`; output in `heisenberg-output.txt`) checks the calibration example.
  `H = Z^(Z) x Z` has product `(v,s)(v',s') = (v+v', s+s'+beta(v,v'))`, where `beta(e_i,e_(i+1)) = 1` and
  `beta` vanishes on all other pairs of basis vectors. The script confirms `[x_i, x_(i+1)] = c` and
  `[x_0^-1 x_1, x_1^-1 x_2] = c^2`. So `G = H ⋊ <shift> = <x_0, t>` has `G''` infinite cyclic and derived
  length 3, and its Hirsch length is infinite.

No coset enumeration was attempted. The metabelian-type enumerations in
`experiments/higman-edge-collapse-2026-09-17` already exceeded `2*10^6` cosets.
