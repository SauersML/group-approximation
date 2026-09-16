---
rg: 2
id: parity-correcting-push-fails-via-minus-one-kernel
kind: route
title: "Conjugate powers of a Brunnian braid in the Burau kernel at t = −1 stay there after inclusion into B_5"
target: parity-correcting-push-fails-for-a-brunnian-four-braid
requires:
  - burau-minus-one-kernel-meets-brunnian-four-braids
  - parity-clean-arc-counts-see-only-burau-mod-t-plus-one
artifacts:
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

Artifact §9, Proposition 9.1.

1. By `burau-minus-one-kernel-meets-brunnian-four-braids`, `Φ_0` is a nontrivial element of
   `Brun_4` with `ρ̄_4(Φ_0) = I`.
2. `ρ̄_4` is a homomorphism. So for all `k ≥ 1` and `y ∈ B_4`,
   `ρ̄_4(Φ_1) = ρ̄_4(y) ρ̄_4(Φ_0)^k ρ̄_4(y)^{-1} = I`, where `Φ_1 = y Φ_0^k y^{-1}`.
3. The standard inclusion `f : B_4 → B_5` sends `σ_i ↦ σ_i` for `i = 1, 2, 3`. From the generator
   matrices, `ρ_5(f(σ_i)) = ρ_4(σ_i) ⊕ 1`. So `ρ_5 ∘ f = ρ_4 ⊕ 1`, and
   `ρ_5(f(Φ_1)) ≡ I_5 mod (t+1)`.
4. Apply part 2 of `parity-clean-arc-counts-see-only-burau-mod-t-plus-one` with `n = 5`,
   `Ψ = f(Φ_1)` and any `Γ ∈ B_5`, in particular any `Γ ∈ K_5`.
   - Any parity-clean transverse representatives of `(β_*^3) f(Φ_1) Γ` and `(β_*^3) Γ` cross `α`
     equally often. ∎
