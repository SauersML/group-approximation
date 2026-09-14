---
rg: 2
id: anti-central-ternary-matrix-ring-proof
kind: route
title: The diagonal endomorphism centralizes the swap and sign units, whose quaternion algebra is a matrix ring
target: anti-central-ternary-summand-contains-its-matrix-ring
requires: []
artifacts:
  - research/artifacts/ternary-anti-central-cohn-reformulation-2026-09-12.md
---

Section 1 of the artifact.

- **The endomorphism.** `t_i s_j = delta_ij` makes `delta(g) = s0 g t0 + s1 g t1` multiplicative, and
  `t0 delta(g) s0 = g` makes it injective. `delta(-1) = -1`, and a direct expansion shows `delta(g)`
  commutes with `w` and with `d`.
- **The matrix ring.** In `S_-`, `[w]^2 = [d]^2 = 1_-` and `[d][w] = -[w][d]`. So
  `span{1_-, [w], [d], [wd]}` is four-dimensional and closed under products, and the matrix units of
  Lemma 7.2 of the invariant-output artifact show it is `M_2(F_3)`.
- **The embedding.** A central simple subalgebra and any subalgebra of its centralizer generate
  their tensor product injectively. That gives `Q (x) delta_*(S_-) ~= M_2(S_-)` inside `S_-`,
  unitally.
- **The consequence.** Iterating gives `M_(2^n)(S_-)` inside `S_-`. A pair `BA = I != AB` in a matrix
  ring pads to size `2^n` and travels along the unital injective embedding to a scalar pair.
