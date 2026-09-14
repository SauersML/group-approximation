---
rg: 2
id: weakly-finite-nonzero-defect-via-sofic-jacobson-image
kind: route
title: Compose the half-line homomorphism with the anti-central summand of the group algebra of its sofic image
target: five-transvection-group-has-weakly-finite-nonzero-defect
requires:
  - five-transvection-group-acts-on-jacobson-half-line
  - jacobson-image-of-five-transvection-group-is-sofic
  - linear-sofic-group-algebra-is-stably-finite
---

## Why sufficient

1. **Stable finiteness.** A sofic group is `F_3`-linear sofic: a permutation `σ` of `n` points moving `δn` of them has
   `rank(P_σ - I) >= δn/2`, and it differs from a product in at most as many rows as the permutations do. So
   `linear-sofic-group-algebra-is-stably-finite` makes `F_3[Γ_V]` stably finite.
2. **The summand.** `ε_- = (1 - [-I])/2` is a central idempotent, and `W = ε_- F_3[Γ_V]` is weakly finite. If `ab = ε_-`
   in `W`, then `(a + ε_+)(b + ε_+) = 1` with `ε_+ = 1 - ε_-`. So `(b + ε_+)(a + ε_+) = 1`, and `ba = ε_-`.
3. **The model.** `ρ(g) = ε_- [ρ_V(g)]` is a homomorphism `Γ_5 -> W^x`, with `ρ_V` from
   `five-transvection-group-acts-on-jacobson-half-line`. Then `ρ(z) = ε_- [-I] = -ε_- = -1_W`.
4. **Nonzero defect.** Over `F_3`, `1/2 = -1`, so `ε_- = [z̄] - 1` with `z̄ = -I`. Writing bars for images in `Γ_V`,
   `D_ρ = ([z̄] - 1)([x̄_23 x̄_12] - [x̄_23] - [x̄_12] + 1)` is a sum of the eight group elements `z̄^e x̄_23^a x̄_12^b` with
   coefficients `±1`. Item 3 of `five-transvection-group-acts-on-jacobson-half-line` says these are distinct, so
   `D_ρ != 0` in `F_3[Γ_V]`.
