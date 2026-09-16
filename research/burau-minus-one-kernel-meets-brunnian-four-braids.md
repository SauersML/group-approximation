---
rg: 2
id: burau-minus-one-kernel-meets-brunnian-four-braids
kind: claim
title: "A nontrivial Brunnian 4-braid has Burau matrix congruent to the identity modulo t+1"
distinct_from:
  four-strand-burau-representation-has-nontrivial-kernel: that claim asks for a nontrivial braid with Burau matrix equal to I over Z[t^{±1}]; this claim gives one whose matrix is I only after t ↦ −1, and is not I itself
  brunnian-four-braids-avoid-burau-kernel: that claim is about the kernel of Burau over Z[t^{±1}]; this claim is about the much larger kernel at t = −1 and says it meets Brun_4 nontrivially
artifacts:
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

Let `ρ_4` be the unreduced Burau representation of `B_4` over `Z[t^{±1}]`, with
`ρ_4(σ_i) = I ⊕ [[1−t, t], [1, 0]] ⊕ I`, and `ρ̄_4 = ρ_4 mod (t+1)`. Put:

- `A_ij = σ_{j−1} ⋯ σ_{i+1} σ_i^2 σ_{i+1}^{-1} ⋯ σ_{j−1}^{-1}`;
- `T = (σ_1σ_2)^6`;
- `b = [A_14, [A_24, A_34]]`;
- `Φ_0 = [T, b] = T b T^{-1} b^{-1}`, a word of length 96.

**Claim.** `Φ_0` lies in the Brunnian subgroup `Brun_4`, `Φ_0 ≠ 1`, `ρ_4(Φ_0) ≠ I`, and
`ρ_4(Φ_0) ≡ I mod (t+1)`.

- Geometrically, `T = Δ_3^4 = T_c^2` for a curve `c` around `p_1, p_2, p_3`.
- More generally, `[T_c^2, Φ]` is a nontrivial element of `Brun_4 ∩ ker ρ̄_4` for every curve `c`
  around three points and every `1 ≠ Φ ∈ Brun_4` (artifact §10.2). That generalization is not
  part of this claim.

Consequence: the faithfulness question for `B_4` lives inside `Brun_4 ∩ ker ρ̄_4`. No certificate
that sees only `𝕄(−1)` can decide it. See
`parity-clean-arc-counts-see-only-burau-mod-t-plus-one`.

Route: `burau-minus-one-kernel-meets-brunnian-four-braids-proof`.
