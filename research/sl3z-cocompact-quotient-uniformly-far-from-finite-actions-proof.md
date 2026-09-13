---
rg: 2
id: sl3z-cocompact-quotient-uniformly-far-from-finite-actions-proof
kind: route
title: Defect-free labels give holonomy homomorphisms into Λ, Bass-Milnor-Serre kills them on unipotents, finite orbits contradict norm drift
target: sl3z-cocompact-quotient-uniformly-far-from-finite-actions
requires:
  - sl3z-cocompact-microstates-carry-flat-lambda-labels
  - bms-sln-z-representations-agree-with-algebraic-ones
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-holonomy-drift-part2-2026-09-13.md
---

Full proof: Section 3 of the part 2 artifact. Take `ε_E < ε_0` with `η(ε_E) < κ/12`, as in
`sl3z-cocompact-microstates-carry-flat-lambda-labels`. Suppose every pair is good at scale `ε_E`.

1. **Holonomy.** `SL_3(Z)` acts on `Ω = V × Λ`, and the stabilizer of `(v,μ)` is the kernel of a
   homomorphism `ρ_v : Γ_v → Λ` on the finite-index stabilizer `Γ_v` of `v`.
2. **Rational rigidity.** Apply Bass--Milnor--Serre Theorem 16.2 to `f = ι∘ρ_v : Γ_v → GL_m(Q)`. There is
   an algebraic `F` agreeing with `f` on a finite-index `Γ' <= Γ_v`. For unipotent `u ∈ Γ'`, `F(u)` is
   unipotent, so `ι(ρ_v(u)) = 1` by hypothesis, and `ρ_v(u) = 1` since `ι` is faithful. `Γ'` contains
   `e_ij^N` for some `N >= 1`, and these generate `E_3(Z,N)`, which has finite index (BMS, p. 60). So
   `ρ_v` has finite image.
3. **Finite orbits.** `ker ρ_v` has finite index in `SL_3(Z)`, so every orbit on `Ω` is finite. Their
   union `O` is finite, invariant, and has no bad pairs.
4. **Drift.** By item 4 of `sl3z-cocompact-microstates-carry-flat-lambda-labels`, `O` has at least a
   proportion `θ_* > 0` of bad pairs. Contradiction. ∎

For `D` a division algebra, left multiplication by `x ∈ D` is unipotent only if `(x − 1)^N = 0`, hence
`x = 1`. So the left regular representation satisfies the hypothesis.
