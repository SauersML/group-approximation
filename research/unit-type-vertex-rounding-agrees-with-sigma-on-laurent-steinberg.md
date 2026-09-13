---
rg: 2
id: unit-type-vertex-rounding-agrees-with-sigma-on-laurent-steinberg
kind: claim
title: In rank at least five, the canonical Laurent Steinberg extension of a unit-type vertex rounding agrees with the model
distinct_from:
  laurent-extension-agrees-iff-inverse-defects-commute: that is the criterion reducing agreement to d commutation conditions; this proves the conditions hold for r >= 5, through property (T) of the mixed-level root group.
  mixed-level-root-group-is-kazhdan-in-rank-at-least-five: that proves K_i is Kazhdan; this consumes it, together with the exact commutation of the inverse-root defects with K_i, to conclude agreement on St_r(L).
  laurent-vertex-rounds-for-every-model: that is full Laurent-vertex rounding, open; this gives agreement on the Steinberg cover St_r(L) only, leaving the K_2 descent to actor models.
artifacts:
  - research/artifacts/hs-extension-laurent-descent-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Setting:
- `R_+ = F_q[x_1..x_d] ⊂ L = F_q[x^(±1)]`, `Γ = EL_r(R_+) < Δ = EL_r(L)`, `r >= 5`, `q : St_r(L) -> Δ`;
- `σ : Δ -> U(prod_U M_n)` a homomorphism;
- genuine `π_n : Γ -> U(n')` with `π = σ` on `Γ`, each factoring through `St_r(A_n)` for a finite quotient `A_n` of
  `R_+` in which every `x_i` is a unit;
- `ρ'_n` the canonical extension of `π_n` to `St_r(L)`.

**Claim.** `σ∘q = ρ'` on `St_r(L)`.

**Proof sketch** (artifact §1).
- **Exact commutation.** The inverse-root defect `W_i = ρ'(x_23(x_i^(-1)))^* σ(e_23(x_i^(-1)))` commutes exactly in `M`
  with every generator `e_cd(x_i^([c=3]+[d=2]) R_+)` of the mixed-level group `K_i`:
  - full roots commute with `e_23`;
  - row 3 and column 2 at level `(x_i)` are handled by the Steinberg cancellation of the criterion's proof;
  - the corner at level `(x_i^2)` is a commutator of those.
- **Same image.** `π_n(K_i) = π_n(Γ)` at every coordinate, because `x_i` is a unit in `A_n`.
- **Kazhdan.** Property (T) of `K_i` moves the coordinates of `W_i` by `o(1)` into `π_n(K_i)' = π_n(Γ)'`. So
  `W_i ∈ π(Γ)' ∩ M`.
- **Conclusion.** Item 2 of `laurent-extension-agrees-iff-inverse-defects-commute` gives agreement.

This writes out as a claim the reduction that `laurent-vertex-rounds-for-every-model` (Attempts, lanes
`nh-laurent-commutant`, `nh-ki-kazhdan`) records as an Attempts bullet.

Derivation: `unit-type-rounding-laurent-steinberg-agreement-proof`.
