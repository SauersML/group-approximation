---
rg: 2
id: f9-hadamard-spectral-idempotents-are-half-idempotents
kind: claim
title: The spectral idempotents of the depth-one Hadamard unit over F_9 are conjugate halves of the unit in the anti-central summand
artifacts:
  - research/artifacts/f9-hadamard-spectral-cohn-attempt-2026-09-12.md
---

Let `G = L_(F_3)(1,2)^x`, `z = -1`, `S_-^(9) = eps_- F_9[G]`, `i^2 = -1` in `F_9`,
`h = s0 t0 + s0 t1 + s1 t0 - s1 t1` and `u = s0 t0 + s1 t0 - s1 t1`. Then `h^2 = z`, `u^2 = 1` and
`u h u = -h`. Put `f_(+/-) = 2(1_- +/- i[h])`.

1. `f_+`, `f_-` are orthogonal idempotents with sum `1_-`, and Frobenius swaps them.
2. `[u] f_+ [u] = f_-`, and `f_+`, `f_-`, `f_+[u]`, `[u]f_+` are matrix units of a unital copy of
   `M_2(F_9)`.
3. `[1_-] = 2[f_+]` in `K_0(S_-^(9))`.
4. If `c f_+ b = 1_-`, then `sigma_1 = f_+ b`, `sigma_2 = [u] f_+ b`, `tau_1 = c f_+`,
   `tau_2 = c f_+ [u]` form a unital two-pair Cohn family.
5. If some subgroup `Gamma` containing `z`, `h`, `u` and the supports of `b`, `c` has a
   characteristic-three rank model moving `z`, then `c f_+ b != 1_-`.

Proof: Section 2 of the artifact, route `f9-hadamard-spectral-half-idempotents-proof`.
