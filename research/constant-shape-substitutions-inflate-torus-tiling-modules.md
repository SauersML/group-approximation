---
rg: 2
id: constant-shape-substitutions-inflate-torus-tiling-modules
kind: claim
title: A constant-shape substitution preserving an SFT inflates torus tiling modules from scale D to scale s_min(D-1)
distinct_from:
  torus-quantum-tilings-decide-matriciality-of-sft-rings: that equates exact matriciality with torus modules at every scale; this produces modules at larger scales from one module when a constant-shape self-similarity exists
  labbe-wang-shift-has-polynomial-pattern-complexity: that uses Labbé's non-constant-shape morphism to count patterns; this needs constant shape and does not apply to Labbé's morphism
artifacts:
  - research/artifacts/un-labbe-torus-decider-inflation-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Ω ⊆ A^(Z^2)` be an SFT, `k` a field, and `σ : A -> A^([0,s_1) × [0,s_2))` a
substitution of constant shape `S = diag(s_1, s_2)` with `σ(Ω) ⊆ Ω`, where `σ(x)(Sn + j) = σ(x(n))_j`. Assume
`s_min = min(s_1, s_2) >= 2` and `D >= 2`, and put `D' = s_min(D - 1)`.

If `V` is a finite-dimensional module of the torus tiling algebra `𝒯_(D,Λ)(Ω,k)`, then `V` is a module of
`𝒯_(D',SΛ)(Ω,k)` through

`f_b(t') = sum_(a : σ(a)_j = b) e_a(p mod Λ)`, where `t' = Sp + j` and `j ∈ [0,s_1) × [0,s_2)`.

For `D >= 3` this raises the scale strictly (`D' >= D + 1`).

**Scope.** Labbé's morphism `ω = αβγ` has letter images of several shapes, so this does not apply to `Ω_U`
(artifact §5).

Route: `constant-shape-substitutions-inflate-torus-tiling-modules-proof` (artifact §3).
