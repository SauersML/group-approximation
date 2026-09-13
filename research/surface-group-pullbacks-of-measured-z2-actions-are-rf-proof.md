---
rg: 2
id: surface-group-pullbacks-of-measured-z2-actions-are-rf-proof
kind: route
title: Proposition H by integer flows, coarse tracking of the commutator, doubling, and squares as commutators
target: surface-group-pullbacks-of-measured-z2-actions-are-rf
requires: [free-group-full-support-invariant-measure-actions-are-rf, rf-subshifts-are-periodic-window-approximable]
artifacts:
  - research/artifacts/un-class-n-conjecture-2026-09-13-part1.md
---

Full proof: artifact part 1, §2 (Proposition H, Steps 0–5).

1. **Nested partitions.** Let `𝒫_0` have mesh `< ε`, `𝒫_(k+1) = 𝒫_k ∨ T_i^(±1)𝒫_k`, and `𝒫 = 𝒫_4`.
2. **Integer flows.** Lemma F (`free-group-full-support-invariant-measure-actions-are-rf`) at `𝒫` gives
   bijections `α, β` of `E = ⊔ E_P` following `T_1, T_2`.
3. **Tracking.** Induction shows that a 4-letter word in `α^(±1), β^(±1)` sends `E_P` into the `𝒫_0`-atom
   containing the matching `T`-image of `P`. For `[α,β]` that image is `P` itself, so `c = [α,β]` preserves each
   coarse block `E_Q`.
4. **Doubling.** On `E × {1,2}`, `c × id` restricted to each block is a square `τ_Q^2`: pair the two copies of each
   cycle into one cycle of twice the length.
5. **Absorption.** For any finite permutation `σ`, a cycle-reversing `ρ` gives `ρσ^(-1)ρ^(-1) = σ`, hence
   `[σ,ρ] = σ^2`. With `σ_Q = τ_Q^(-1)`, put `α_2 = ⊔ σ_Q`, `β_2 = ⊔ ρ_Q` and the remaining handles trivial. Then
   `∏[α_i,β_i] = id`, so the model is a genuine `Γ_g`-set.
6. **Closeness.** Handle 1 is `ε`-close by tracking; handle 2 stays inside coarse atoms (`q(a_2) = q(b_2) = 0`);
   the image is dense. Lemmas 1–2 (artifact of `rf-subshifts-are-periodic-window-approximable`) finish.
