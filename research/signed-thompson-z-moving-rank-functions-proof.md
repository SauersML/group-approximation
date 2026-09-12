---
rg: 2
id: signed-thompson-z-moving-rank-functions-proof
kind: route
title: Restrict to the unsigned V in one direction and pull back along the centralizer embedding into V in the other
target: signed-thompson-z-moving-rank-functions-match-v-rank-functions
requires: [thompson-v-finitely-presented-infinite-simple, simple-group-rank-functions-are-augmentation-or-detecting]
artifacts:
  - research/artifacts/signed-thompson-minus-one-gate-is-v-rank-gate-2026-09-12.md
---

## Why sufficient

Artifact Theorem 2.1.
- **(2) ⟺ (3).** `N_rk cap V` is normal in the simple group `V`.
- **(1) ⟹ (2).** Suppose `V <= N_rk`. For `g in V`, `g tau g^-1 tau^-1 in N_rk`, so `tau_(gA) ≡ tau_A`.
  - By transitivity of `V` on proper nonempty clopens (artifact Lemma 1.2), all such `tau_A` share one class `c`.
  - `tau_[0] = tau_[00] tau_[01]` forces `c = c^2 = 1`.
  - Then `z = tau_[0] tau_[1] in N_rk`, contradicting `rk(1 - [z]) > 0`.
- **(3) ⟹ (1).** Artifact Lemma 1.1 gives a homomorphism `phi : H -> V' ~= V` with `phi(z) = σ_0 != 1`.
  - A detecting `rk` on `K[V']` has `rk(1 - [σ_0]) > 0`.
  - `rk ∘ phi_K` is a Sylvester matrix rank function on `K[H]`, because `phi_K` is a unital ring map, and it moves `z`.

`N_rk` is a normal subgroup by `simple-group-rank-functions-are-augmentation-or-detecting`. Its augmentation
criterion is used only to name case (2).

*Verified independently by `w4-vf-gate` (2026-09-12), Section 21.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
